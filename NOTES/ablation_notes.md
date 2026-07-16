# confirmed that later steps take longer to compile, my main reason for the methodology:
For Prop04 of Book2:

  ┌───────────┬──────┬───────────────────────────────┬─────────────────────────────┐
  │   build   │ wall │ frontier (deepest error line) │           regime            │
  ├───────────┼──────┼───────────────────────────────┼─────────────────────────────┤
  │ build.log │ 672s │ ~84–152 (many steps failing)  │ timeout-dominated (outlier) │
  ├───────────┼──────┼───────────────────────────────┼─────────────────────────────┤
  │ build2    │ 108s │ line 157                      │                             │
  ├───────────┼──────┼───────────────────────────────┼─────────────────────────────┤
  │ build3    │ 104s │ line 157                      │                             │
  ├───────────┼──────┼───────────────────────────────┼─────────────────────────────┤
  │ build4    │ 204s │ line ~164                     │                             │
  ├───────────┼──────┼───────────────────────────────┼─────────────────────────────┤
  │ build5    │ 204s │ line ~164–173                 │                             │
  ├───────────┼──────┼───────────────────────────────┼─────────────────────────────┤
  │ build7    │ 264s │ line ~226–229                 │                             │
  ├───────────┼──────┼───────────────────────────────┼─────────────────────────────┤
  │ build6    │ 267s │ line ~233–244                 │                             │
  ├───────────┼──────┼───────────────────────────────┼─────────────────────────────┤
  │ build8    │ 379s │ full file compiles (EXIT 0)   │                             │
  ├───────────┼──────┼───────────────────────────────┼─────────────────────────────┤
  │ clean     │ 355s │ full file (EXIT 0)            │                             │
  └───────────┴──────┴───────────────────────────────┴─────────────────────────────┘

- After the fact, yes naive llm is better. My original motiviation was I did not know how bad this is gonna get since they are new proofs. 


# Why is mine so much longer

● Pinpointed. No more guessing — here's the full attribution with the numbers behind each claim.

  The cost driver is cache_read (context re-read every turn). Methodology = 2.86× ablated. It decomposes exactly:

  ┌───────────────────────────────┬─────────────┬─────────────┬────────────────────┐
  │            factor             │ methodology │   ablated   │       ratio        │
  ├───────────────────────────────┼─────────────┼─────────────┼────────────────────┤
  │ turns (API calls)             │ 509         │ 299         │ 1.70×              │
  ├───────────────────────────────┼─────────────┼─────────────┼────────────────────┤
  │ typical context/turn (median) │ 294,615 tok │ 183,177 tok │ 1.61×              │
  ├───────────────────────────────┼─────────────┼─────────────┼────────────────────┤
  │ → cache_read total            │ 147.6M      │ 51.6M       │ 2.86× (=1.70×1.61) │
  └───────────────────────────────┴─────────────┴─────────────┴────────────────────┘

  Neither factor alone explains it — they multiply. So "more turns" is real but it's only half the story; the context is also 1.6× fatter per turn, and every turn pays for both.

  What makes the context 1.6× fatter — measured, not guessed:

  1. Fatter starting prompt: 44,098 vs 20,971 tokens (2.1×). This is the fixed methodology payload — CLAUDE.md methodology sections + skill files (faithful-prove/prove-euclid SKILL.md, which I can see being read)
  + recalled memory. It's paid on every one of 509 turns. That ~23k-token delta × 509 turns ≈ 11.7M cache_read tokens of pure fixed tax the ablated arm never pays.
  2. check_step/--drive OUTPUT is the single largest injected blob: 182,804 chars (~46k tok) vs 1,458 chars in ablated. This is the precise correction to your instinct: the drive script costs 0 tokens — you're
  right — but its output is dumped into context and re-read on every subsequent turn. Drive doesn't cost CPU-in-tokens; it costs by volume of text it prints back, amplified by however many turns follow it.

  Your six hypotheses, scored against the data:

  ┌─────────────────────────────────────────────┬─────────────────────────┬───────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
  │                 your guess                  │         verdict         │                                                   evidence                                                    │
  ├─────────────────────────────────────────────┼─────────────────────────┼───────────────────────────────────────────────────────────────────────────────────────────────────────────────┤
  │ more turns from one-step-one-check          │ ✅ confirmed            │ 509 vs 299 (1.70×)                                                                                            │
  ├─────────────────────────────────────────────┼─────────────────────────┼───────────────────────────────────────────────────────────────────────────────────────────────────────────────┤
  │ drive spends 0 tokens                       │ ⚠️ half-right           │ script yes; but its output = 183k chars, the #1 content blob, re-read every turn                              │
  ├─────────────────────────────────────────────┼─────────────────────────┼───────────────────────────────────────────────────────────────────────────────────────────────────────────────┤
  │ reading the whole (longer) codebase         │ ❌ rejected             │ methodology read less code: 52k vs 78k chars of file reads                                                    │
  ├─────────────────────────────────────────────┼─────────────────────────┼───────────────────────────────────────────────────────────────────────────────────────────────────────────────┤
  │ denied commands thrashing                   │ ❌ rejected             │ only 13 error results (vs 4), and most are benign "read-before-write" reminders / one skill read — negligible │
  ├─────────────────────────────────────────────┼─────────────────────────┼───────────────────────────────────────────────────────────────────────────────────────────────────────────────┤
  │ lemma signatures cause more thought         │ ⚠️ minor                │ folded into the fixed 44k prompt; not a driver                                                                │
  ├─────────────────────────────────────────────┼─────────────────────────┼───────────────────────────────────────────────────────────────────────────────────────────────────────────────┤
  │ agent fighting methodology / wants one-shot │ ⚠️ smallest real factor │ output tokens 824k vs 641k = only 1.28×                                                                       │
  └─────────────────────────────────────────────┴─────────────────────────┴───────────────────────────────────────────────────────────────────────────────────────────────────────────────┘

  So the true ranking of causes: (1) 1.6× fatter context — split between the loaded skills/memory baseline and the accumulated check_step output — × (2) 1.7× more turns from forced one-step-one-check. Denials and
  codebase-reading are not causes. The one-shot-fighting is real but the weakest contributor.

