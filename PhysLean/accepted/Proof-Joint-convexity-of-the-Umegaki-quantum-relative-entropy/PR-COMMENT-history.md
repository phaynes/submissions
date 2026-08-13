# PR #1378 — commit-history note (for Philip to post as a PR comment)

Per AI-POLICY §3.1 you post this yourself. Paste it as a comment on the PR so the
two-commit history is self-explanatory. (If you'd rather squash later, this note is
harmless and can be edited/deleted.)

---

A note on the two commits: the first commit is the initial proof; the second is a
refactor of it — reducing the number of `have` statements and extracting the mixture
plumbing, the α→1⁺ continuity step, and the `ENNReal.ofReal` identity into small named
lemmas, plus a `Mixable.mix_one` simp lemma. The net diff is the refactored state. Happy
to squash to a single commit if you'd prefer a cleaner history for merge.
