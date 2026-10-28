// Loaded only from the workflow's trusted default-branch revision.
const fs = require('node:fs');

async function authorize({ github, context, core }) {
  const { comment, issue } = context.payload;
  if (!issue.pull_request || comment.body !== '!review' || comment.user.type !== 'User') return;
  const { data: access } = await github.rest.repos.getCollaboratorPermissionLevel({
    ...context.repo, username: comment.user.login,
  });
  if (!['admin', 'maintain', 'write'].includes(access.permission)) {
    core.notice('!review requires repository write access.');
    return;
  }
  const { data: pr } = await github.rest.pulls.get({
    ...context.repo, pull_number: issue.number,
  });
  if (pr.state !== 'open') return;
  for (const sha of [pr.head.sha, pr.base.sha]) {
    if (!/^[0-9a-f]{40}$/.test(sha)) throw new Error('Invalid commit SHA');
  }
  core.setOutput('head', pr.head.sha);
  core.setOutput('base', pr.base.sha);
  core.setOutput('allowed', 'true');
}

async function collect({ github, context }) {
  const { HEAD_SHA: head, BASE_SHA: base, MERGE_BASE: mergeBase } = process.env;
  const args = { ...context.repo, pull_number: context.issue.number };
  const { data: pr } = await github.rest.pulls.get(args);
  if (pr.head.sha !== head || pr.base.sha !== base) throw new Error('PR changed; run !review again.');
  const comments = await github.paginate(github.rest.issues.listComments, {
    ...context.repo, issue_number: context.issue.number, per_page: 100,
  });
  const checks = await github.paginate(github.rest.checks.listForRef, {
    ...context.repo, ref: head, per_page: 100,
  });
  const statuses = await github.paginate(github.rest.repos.listCommitStatusesForRef, {
    ...context.repo, ref: head, per_page: 100,
  });
  fs.writeFileSync('.codex-review/context.json', JSON.stringify({
    head, baseTip: base, mergeBase,
    title: pr.title, body: pr.body, draft: pr.draft,
    labels: pr.labels.map(label => label.name),
    comments: comments.map(c => ({ author: c.user.login, body: c.body, url: c.html_url })),
    checks: checks.map(c => ({ name: c.name, head: c.head_sha, status: c.status,
      conclusion: c.conclusion, url: c.details_url, output: c.output })),
    statuses: statuses.map(s => ({ context: s.context, state: s.state,
      description: s.description, url: s.target_url })),
  }, null, 2));
}

function render({ message, result, head, base, mergeBase, currentHead, currentBase, runUrl }) {
  let body = result === 'success' && message.trim()
    ? message.trim()
    : `Review could not complete. Check the [workflow logs](${runUrl}), then post \`!review\` again.`;
  if (body.length > 24000) body = body.slice(0, 24000) + '\n\n[Review output truncated.]';
  if (head !== currentHead || base !== currentBase) {
    body = '**Outdated review: the PR head or base changed during this run. Post `!review` again.**\n\n' + body;
  }
  return body + `\n\n---\nCodex quick review · head \`${head}\` · base tip \`${base}\` · merge base \`${mergeBase || 'unavailable'}\`\n` +
    `Static inspection only; builds, lint, trust audits, extraction, and benchmarks were not run by this bot. ` +
    `AI assistance, not human approval. [Workflow run](${runUrl}).`;
}

async function publish({ github, context }) {
  const { data: pr } = await github.rest.pulls.get({
    ...context.repo, pull_number: context.issue.number,
  });
  if (pr.state !== 'open') return;
  const body = render({
    message: process.env.REVIEW_MESSAGE || '', result: process.env.REVIEW_RESULT,
    head: process.env.HEAD_SHA, base: process.env.BASE_SHA, mergeBase: process.env.MERGE_BASE,
    currentHead: pr.head.sha, currentBase: pr.base.sha,
    runUrl: `${process.env.GITHUB_SERVER_URL}/${context.repo.owner}/${context.repo.repo}/actions/runs/${context.runId}`,
  });
  await github.rest.issues.createComment({
    ...context.repo, issue_number: context.issue.number, body,
  });
}

module.exports = { authorize, collect, render, publish };
