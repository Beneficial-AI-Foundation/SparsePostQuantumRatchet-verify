# Performance Tracking
We use Lean's [Radar](https://github.com/leanprover/radar) utility for profiling. See its associated Github page for more information.
The `Request Radar` workflow comments `!radar` automatically when a non-draft PR
is opened or reopened, receives new commits, or is marked ready for review.
Draft PRs are skipped. Re-running the workflow does not post another request
for the same base/head commit pair. You can still comment `!radar` manually
to request a report, including on a draft PR or to retry a failed request.

Our `baif-radar` bot replies with a short summary of noteworthy changes and a
link to the full report. Before approving, check that the report covers the
current PR head commit, that both benchmark builds succeeded, and that any
performance regressions are acceptable. Radar chooses the merge base as its
comparison commit; this may differ from the tip of the PR's target branch.

A successful `Request Radar benchmark` check means only that the request was
posted (or already existed), not that benchmarking finished or performance
passed. It is not a performance merge gate. Results are reviewed manually.

When enabling this workflow, verify on a PR that `baif-radar` accepts the
comment from `github-actions[bot]` and returns a report for the current commit.
Radar can restrict command authors through `allowedAuthorAssociations`; the
deployed server must permit the automation identity. If it rejects the request,
ask the Radar administrator to configure an appropriate authorized integration
and use a manual `!radar` comment from an authorized reviewer in the meantime.
Do not broadly relax command permissions just to allow the automation.

The workflow uses `pull_request_target` so it can comment on fork PRs. It only
reads PR metadata and writes comments; never add checkout or execution of PR
code to this privileged workflow.

An exhaustive collection of metrics for this repository can be found [here](https://radar.18.118.100.156.nip.io/) and is available for public use.
