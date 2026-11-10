const { test } = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');

// Execute the actual inline workflow scripts without checking out or running PR code.
const workflow = fs.readFileSync(path.join(__dirname, '../.github/workflows/radar.yml'), 'utf8');
const scripts = [...workflow.matchAll(/          script: \|\n((?:            .*\n|\n)+)/g)]
  .map(match => match[1].replace(/^            /gm, ''));
assert.equal(scripts.length, 2);
const AsyncFunction = Object.getPrototypeOf(async function () {}).constructor;

function fixture() {
  const pr = { state: 'open', draft: false, author_association: 'MEMBER',
    number: 805, head: { sha: 'head' }, base: { sha: 'base', ref: 'main' } };
  const eventPR = structuredClone(pr);
  const outputs = {};
  const comments = [];
  const messages = [];
  const existing = [];
  const context = { repo: { owner: 'owner', repo: 'repo' }, payload: { pull_request: eventPR } };
  const github = { rest: {
    pulls: { get: async () => ({ data: pr }) },
    users: { getAuthenticated: async () => ({ data: { login: 'baif-radar' } }) },
    issues: { listComments() {}, createComment: async comment => comments.push(comment) },
  }, paginate: async () => existing };
  const core = { info: message => messages.push(message),
    setOutput: (key, value) => { outputs[key] = value; },
    summary: { addRaw(message) { messages.push(message); return this; }, async write() {} } };
  return { pr, eventPR, outputs, comments, messages, existing,
    run: index => new AsyncFunction('github', 'context', 'core', scripts[index])(github, context, core) };
}

test('eligible current PR proceeds despite stale event draft/association', async () => {
  const f = fixture();
  f.eventPR.draft = true;
  f.eventPR.author_association = 'NONE';
  await f.run(0);
  assert.equal(f.outputs.allowed, 'true');
  await f.run(1);
  assert.equal(f.comments.length, 1);
  assert.equal(f.comments[0].body, '!radar\n\n<!-- radar-request:base:head -->');
});

test('closed, draft, untrusted, and superseded PRs are rejected with a reason', async () => {
  for (const mutate of [
    f => { f.pr.state = 'closed'; },
    f => { f.pr.draft = true; },
    f => { f.pr.author_association = 'CONTRIBUTOR'; },
    f => { f.pr.head.sha = 'new'; },
    f => { f.pr.base.ref = 'other'; },
  ]) {
    const f = fixture();
    mutate(f);
    await f.run(0);
    assert.equal(f.outputs.allowed, 'false');
    assert.ok(f.messages.some(message => message.startsWith('Radar not requested:')));
    await f.run(1);
    assert.equal(f.comments.length, 0);
  }
});

test('permission change between steps prevents posting', async () => {
  const f = fixture();
  await f.run(0);
  assert.equal(f.outputs.allowed, 'true');
  f.pr.author_association = 'NONE';
  await f.run(1);
  assert.equal(f.comments.length, 0);
});

test('existing request by the Radar account prevents a duplicate', async () => {
  const f = fixture();
  f.existing.push({ user: { login: 'baif-radar' },
    body: '!radar\n\n<!-- radar-request:base:head -->' });
  await f.run(1);
  assert.equal(f.comments.length, 0);
});
