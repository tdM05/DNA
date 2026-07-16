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

# also confirmed mine does NOT grow:
    #  | clock    | wall  | check mode  | target
  -----+----------+-------+-------------+--------------------
     1 | 07:35:16 |    1s | status      |
     2 | 07:35:22 |    0s | check       |            (+deps)
     3 | 07:36:49 |   67s | provable    |            (all steps)
     4 | 07:38:22 |    6s | context     | step1
     5 | 07:38:58 |   21s | run         | step1
     6 | 07:39:28 |    7s | context     | step2      (+scaffold)
     7 | 07:40:13 |   13s | context     | step3
     8 | 07:40:46 |   45s | drive       |
     9 | 07:42:19 |   27s | drive       |
    10 | 07:42:57 |   26s | drive       |
    11 | 07:43:34 |   18s | drive       |
    12 | 07:47:08 |    6s | context     | step5      (+scaffold)
    13 | 07:51:37 |   45s | provable    | step5
    14 | 07:52:33 |   45s | provable    | step5
    15 | 07:53:41 |   45s | provable    | step5
    16 | 07:55:21 |   45s | provable    | step5
    17 | 07:57:03 |    5s | provable    | step5
    18 | 07:57:11 |    2s | provable    | step5
    19 | 07:58:05 |    0s | (grep script, not a check)
    20 | 08:01:32 |   35s | provable    | step5_bgd
    21 | 08:04:08 |   35s | provable    | step5_bgd
    22 | 08:05:05 |    4s | provable    | step5_bgd
    23 | 08:05:15 |   34s | provable    | step5_ss
    24 | 08:06:23 |    5s | provable    | step5_ss
    25 | 08:06:45 |   50s | drive       |
    26 | 08:08:07 |    6s | context     | step6      (+scaffold)
    27 | 08:09:11 |    5s | provable    | step6
    28 | 08:09:20 |    4s | provable    | step6
    29 | 08:10:11 |    5s | provable    | step6
    30 | 08:10:21 |   21s | drive       |
    31 | 08:11:55 |   34s | drive       |
    32 | 08:13:47 |   39s | provable    | step8
    33 | 08:15:02 |   34s | drive       |
    34 | 08:19:35 |   64s | drive       |
    35 | 08:21:09 |   47s | drive       |
    36 | 08:22:25 |   49s | drive       |
    37 | 08:23:45 |   23s | drive       |
    38 | 08:24:32 |   22s | drive       |
    39 | 08:25:45 |    5s | provable    | step14_assumption1
    40 | 08:25:55 |   23s | drive       |
    41 | 08:27:37 |   39s | drive       |
    42 | 08:32:28 |   51s | drive       |
    43 | 08:34:06 |   25s | drive       |
    44 | 08:34:35 |    7s | provable    | step16
    45 | 08:35:18 |    4s | provable    | step16
    46 | 08:35:58 |    7s | provable    | step16
    47 | 08:37:17 |   85s | drive       |
    48 | 08:39:14 |    4s | status      |
    49 | 08:39:57 |   47s | subtree     | step17
    50 | 08:41:21 |   25s | drive       |
    51 | 08:42:24 |   27s | drive       |
    52 | 08:43:24 |   27s | drive       |
    53 | 08:44:53 |   56s | drive       |
    54 | 08:57:07 |   60s | drive       |
    55 | 08:58:40 |   67s | drive       |
    56 | 08:59:55 |   67s | drive       |
    57 | 09:01:30 |  120s | drive       |
    58 | 09:05:18 |    0s | drive       |   (cached, no edits)
    59 | 09:07:29 |   83s | drive       |
    60 | 09:09:26 |   60s | drive       |
    61 | 09:16:42 |    0s | drive       |   (cached)
    62 | 09:17:21 |    0s | status      |
    63 | 09:17:25 |    0s | status      |
    64 | 09:17:39 |    0s | status      |
    65 | 09:17:46 |    7s | status      |
    66 | 09:18:03 |    0s | drive       |   (cached)
    67 | 09:19:01 |    8s | status      |
    68 | 09:19:47 |    1s | drive       |   (cached)
    69 | 09:20:15 |    8s | status      |


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

