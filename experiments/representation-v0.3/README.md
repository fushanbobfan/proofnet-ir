# Representation-as-target model study v0.3

representation-v0.2 found that one local model answering without thinking verifies no derivation, with
positions or with stable labels, and six proof nets. This study asks the same question of a model that reasons
before it answers. Every arm runs under two conditions of Qwen3.8-27B: `direct`, with thinking off, and
`thinking`, with thinking on at the chat template's highest effort and a server thinking budget of 6,144
tokens. The two conditions share the sampling settings, so they differ only in thinking.

## Arms and settings

- `proof`, `proofIds`, `net`: representation-v0.2's position-based derivation, labelled derivation (converted
  to positions before Lean verifies it), and axiom linking, with v0.2's prompts, renderings, and verification
  (`proofnet_ir_representation_verify`);
- corpus: the 90 positives of `experiments/model-v0.2` (depth 2, 3, and 4; unique, one-label, and two-label
  names; 10 per stratum);
- model: `Qwen3.8-27B-UD-Q4_K_XL` on llama.cpp build 11193, six requests at a time, temperature 0.6, top-p
  0.95, top-k 20, seed 20260921, 8,192 completion tokens. No grammar constrains the answers: with thinking on,
  the server applies a grammar to the thinking as well, which leaves no room to think (checked before
  registration).

## Artifacts

- `preregistration.json`: arms, conditions, prompts by hash, model and server settings, hypotheses H74 to
  H77, checks C20 and C21, and the pilot's outcome, committed in `d2dab38` before any response existed;
- `amendment-1.json`: the handling of server failures (below), committed in `47940a1` when 387 of the 540
  responses had been collected and none had been parsed or verified;
- `raw-responses.jsonl`: the 540 responses in the analysis, verbatim, with request hashes and elapsed times;
- `server-failures.jsonl`: the 19 responses set aside under the amendment;
- `results.jsonl`, `summary.json`, `report.md`: verdicts, both analyses, and the decisions.

## Reproduction

```text
python scripts/run_representation_v3.py --check-committed
```

This re-verifies every committed proposal with Lean, recomputes the primary and the as-registered analyses,
and checks the hashes; CI runs it. `--run` collects the responses again from a local server, which took about
29 hours of generation here and is not deterministic across batches, hardware, or server builds.

## Outcome

- **H74 holds**: with thinking, labelled derivations verified 32 of 90 positives, against none without
  thinking (32 against 0 on the discordant tasks, one-sided p = 2.3e-10, Holm-adjusted 9.3e-10).
- **H75, H76, and H77 do not hold**: with thinking, nets verified 35, labelled derivations 32, and position
  derivations 30. The discordant tasks are 7 against 4 for nets over labelled derivations, 4 against 7 the
  other way, and 5 against 3 for labelled over position derivations; none is significant after Holm's
  adjustment.
- Without thinking the earlier pattern returns: no derivation verified in either format, and nets verified 11,
  seven of them depth-2 sequents with unique labels.
- Depth bounds all three formats alike. With thinking, the arms verified 27, 27, and 28 of the 30 depth-2
  positives, 3, 5, and 7 of the 30 at depth 3, mostly with unique labels, and none of the 30 at depth 4.
- Verified thinking answers used a median of 5,205 (position), 4,331 (labelled), and 5,835 (net) completion
  tokens; the verified direct nets used 22. Unverified thinking derivations were mostly unparseable (29
  position and 22 labelled answers, 12 of them cut off at the token limit) or broke a rule at a position or
  label that does not hold the named connective.
- **C20, C21, and C22 hold**: no request in the analysis failed, 15 of the 270 thinking answers stopped at the
  token limit (5.6%), and no response in the primary analysis is a server failure.

## Server failures and amendment 1

During the run, a server slot occasionally turned an answer into '/' repeated to the token limit, and
once a slot had failed, its later answers failed as well until the server restarted; the same symptom is
reported upstream for Qwen hybrid models (llama.cpp issues 23577 and 26209). The amendment makes such a
response, one that ends at the token limit in at least 1,000 repetitions of one non-whitespace character, a
server failure: it is set aside and its request sent again, at most three times in all, on a restarted
server. 19 responses to 17 requests were set aside (3 direct, 16 thinking; 3 position, 8 labelled, 8 net). As
registered, with each request's first failure in place, the decisions are the same (H74 holds, 28 against 0;
H75 to H77 do not), and C21 fails, with 29 of 270 thinking answers at the limit.

## Operation

The responses were collected from 2026-09-28 10:47 to 2026-09-30 07:21. The server was restarted after the
amendment and after later server failures, four times in all, three of them by a supervisor script that
started it from the registered command line and checked the build and the slot count at each start; every
response carries the registered build's fingerprint. Twice, with the laptop's battery charge limit active, a
loss of mains power of a few seconds left the machine generating at about a third of its speed. 42 requests
reached the runner's one-hour timeout; the run was paused, and they were sent again, as the runner does for
failed requests, once a reboot and then turning the charge limit off had restored the speed. For about five
minutes a second server from an unrelated test shared the port; no request was sent in that window.

## Interpretation boundary

For this model, thinking decides whether derivations verify at all, and with thinking the three formats show
no significant difference: each verifies about a third of the positives, all at depth 2 or 3. The nets' lead in
v0.1 and v0.2, which this study reproduces without thinking, shrinks with thinking to 35 against 32 and 30, largest
on depth-3 sequents with unique labels; much of it therefore comes from answering without reasoning, though a
smaller format effect is not excluded. The study covers one quantized model, one prompt
design per format, one thinking budget, and unit-free, cut-free MLL; a non-significant difference is not
evidence that the formats are equal, and depth 4 is beyond every format at this budget.
