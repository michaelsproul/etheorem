"""The pyspec tests: one parametrized test per vector case, plus one corpus-wide
scope check on the caught set (`test_value_error_scope`).

The harness builds a request from the case on disk and submits it to the
worker's Lean server; the server returns the driver's classify result. The
assertion follows the reject-faithfulness audit (`SPECS_ARCHITECTURE.md` §10.2):

- `bug` (`outOfBounds` / `missingKey` on well-formed input, or a server crash) is
  always a hard failure, the bug-smell the audit hunts for;
- `todo` (an unimplemented branch we intend to fill) is `xfail`, the Phase-2
  work-queue: it does not fail the run, but it is visible and a vector that reaches
  it never passes silently;
- `skip` (a branch we deliberately do not model, an out-of-scope runner or type) is
  `pytest.skip`: it is not a failure and not work-queue, so it never inflates the
  `xfail` count;
- otherwise the case must `pass` (a valid vector's root matched, or an invalid
  vector rejected the way its own reference wrapper expects, which for almost every
  case is an `assert`).

As Phase 2 fills the `todo` stubs, the `xfail`s turn into passes with no test
change. The `skip`s stay skipped, they are out of scope by design.
"""

import pytest

from harness import PINNED_VERSION, build_request, ensure_archive, walk_cases

# Upstream vectors that contradict the spec text. Each id is an open row in
# docs/DISCREPANCIES.md. A pass means the vector now matches the spec, so the
# row and this set have to come out together. Empty at v1.7.0-beta.4: the Heze
# `fork_base_state` vectors, the two alpha.12 rows, match the spec there.
SPEC_TEXT_DIVERGENCES: set[str] = set()

# Vectors of the pinned release that the Lean bodies depart from on purpose. The Fulu to
# Gloas upgrade is the one of the consensus-specs branch `dapplion:gloas-onboard-cutoff`,
# which differs from the pinned release in two places (docs/DISCREPANCIES.md, "Gloas"):
#
# * `upgrade_to_gloas` unsets the payload-availability bit of the fork slot (upstream #5808),
#   so the post-state of every upgrade has another root;
# * `onboard_builders_from_pending_deposits` leaves a builder deposit at or below the
#   onboarding cutoff in the queue.
#
# So every pinned Gloas `fork` case departs, and every pinned Gloas `transition` case that
# has a post-state to compare. A pass means the pinned release and the Lean bodies agree
# again, so the rule and the DISCREPANCIES.md rows have to come out together.
PINNED_TRANSITION_CASES_WITHOUT_POST: set[str] = {
    # The block is rejected, so the case compares no post-state.
    "transition_rejects_pre_gloas_payload_attestation",
}


def departs_from_pinned_release(case) -> bool:
    """`True` for a pinned-release vector whose post-state the Lean upgrade does not match."""
    if case.fork != "gloas":
        return False
    if case.runner == "fork":
        return True
    return case.runner == "transition" and case.name not in PINNED_TRANSITION_CASES_WITHOUT_POST


def test_value_error_scope(request):
    """The `except ValueError` set models one test function's own wrapper,
    `test_invalid_large_withdrawable_epoch`. `RunnerCaughtSet.ofCase` selects that set for the
    whole `epoch_processing`/`registry_updates` pair, so a second post-less case under the pair
    would have its `.arithmetic` reject admitted too. This test fails when the corpus holds one.

    The walk ignores `--subset`, because the claim covers the whole corpus.
    """
    cfg = request.config
    preset = cfg.getoption("--preset")
    fork = cfg.getoption("--fork")
    root = ensure_archive(cfg.getoption("--tag"), preset)
    unexpected = sorted(
        c.case_id
        for c in walk_cases(root, preset, fork)
        if c.runner == "epoch_processing"
        and c.handler == "registry_updates"
        and not (c.path / "post.ssz_snappy").exists()
        and c.name != "invalid_large_withdrawable_epoch"
    )
    assert not unexpected, (
        f"new post-less case(s) under epoch_processing/registry_updates: {unexpected}. "
        f"Check each case's reference wrapper against RunnerCaughtSet.ofCase."
    )


def test_case(case, server, tmp_path, pytestconfig):
    request = build_request(case, tmp_path)
    result = server.submit(request)
    # Before the bug check on purpose: a recorded deviation shows as a post-state root
    # mismatch, which the server reports in the `bug` bucket. The rule reads the pinned
    # vectors alone: vectors of another tag, such as ones generated from the branch, are held
    # to the plain pass criterion.
    if pytestconfig.getoption("--tag") == PINNED_VERSION and departs_from_pinned_release(case):
        if result.passed:
            pytest.fail(
                f"{case.case_id} now matches the pinned release; update "
                "`departs_from_pinned_release` and DISCREPANCIES.md"
            )
        pytest.xfail(
            "the Lean upgrade departs from the pinned release on purpose; see DISCREPANCIES.md"
        )
    if result.bucket == "bug":
        pytest.fail(f"{case.case_id}: bug-smell — {result.detail}")
    # After the bug check on purpose: a bug is always a hard failure, divergence or not.
    if case.case_id in SPEC_TEXT_DIVERGENCES:
        if result.passed:
            pytest.fail(
                f"{case.case_id} now matches the spec; remove it from "
                "SPEC_TEXT_DIVERGENCES and DISCREPANCIES.md"
            )
        pytest.xfail(
            "upstream vector contradicts the spec text; see DISCREPANCIES.md"
        )
    if not result.passed and result.bucket == "skip":
        pytest.skip(f"out of scope (not modeled): {result.detail}")
    if not result.passed and result.bucket == "todo":
        pytest.xfail(f"unimplemented (Phase 2 work-queue): {result.detail}")
    assert result.passed, f"{case.case_id}: {result.bucket} — {result.detail}"
