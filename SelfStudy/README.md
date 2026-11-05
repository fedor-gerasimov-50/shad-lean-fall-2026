# Studying the SHAD Lean course independently

Prepared 21 October 2026. **Recommended pace: 28 study weeks at your stated 3–4 hours per week**, with a two-week winter break built into the calendar. You are new to Lean and already comfortable with mathematical proofs. The core target is **21 May 2027**, followed by an optional four-week bonus block. These are planning estimates, not the course's official deadlines or a guarantee of mastery.

Use the **course as the backbone**, **Mathematics in Lean (MIL) as your practice book**, and **Theorem Proving in Lean 4 (TPiL) to understand the language and foundations**. Read the books alongside the assignments. Finishing both books before starting the homework would postpone the practice that makes their explanations meaningful.

Start with [Syllabus.md](Syllabus.md), keep the [printable syllabus](output/pdf/Syllabus.pdf) nearby, and record only completed evidence in [Progress.md](Progress.md). This folder is the only addition made for this study plan. No homework has been solved for you.

## What is actually in the repository

This is a growing course repository, not a complete semester syllabus. The local checkout is commit `381add80c4008c04b487e3660d06eedf014a7d2e`, dated 14 October 2026, with message `analysis homework`. A read-only check of the upstream default branch on 21 October found the same latest commit. There are **six lecture files and eleven homework files**, including the introductory exercise and the bonus assignment. No video links, video runtimes, official homework deadlines, or full future lecture schedule are supplied here.

| Location | What it contains | How you should use it |
| --- | --- | --- |
| [`README.md`](../README.md) | Russian course introduction and setup instructions | Follow its project setup, using the pinned version. |
| [`Shad/Lectures/`](../Shad/Lectures/) | Interactive Lean demonstrations, examples, exercises, and deliberate errors | Open the matching file while watching the corresponding video. Reconstruct examples in a separate practice file. |
| [`Shad/Homework/HelloLean/Hello/Solution.lean`](../Shad/Homework/HelloLean/Hello/Solution.lean) | A deliberately failing first exercise | Learn how to read a goal and get editor feedback. |
| [`Shad/Homework/Logic/`](../Shad/Homework/Logic/) | Propositional logic, quantifiers, induction | Your first substantial assignments. Read each file's tactic restrictions. |
| [`Shad/Homework/Types/`](../Shad/Homework/Types/) | Functions and counterexamples, convex sets, binary trees | Connect proofs to definitions, programs, and structural induction. |
| [`Shad/Homework/Analysis/`](../Shad/Homework/Analysis/) | Partial sums of `1 / sqrt(n)`, irrationality of `e`, Newton convergence | Longer formalizations requiring library navigation and auxiliary lemmas. |
| [`Shad/Homework/Bonus/Cantor/`](../Shad/Homework/Bonus/Cantor/) | Cantor and Cantor–Bernstein theorems | An extension after functions and sets; the second theorem is a substantial project. |
| [`Test.lean`](../Test.lean) | `import Mathlib` and `#check TopologicalSpace` | An environment smoke check, not a homework checker. |
| [`Shad.lean`](../Shad.lean) | A Mathlib import and a small greeting definition | A library root; it does not import all homework or lectures. |
| [`lean-toolchain`](../lean-toolchain), [`lakefile.lean`](../lakefile.lean), [`lake-manifest.json`](../lake-manifest.json) | Lean `v4.33.1`, Mathlib `v4.33.1`, and locked dependency revisions | Keep these pins. A book example using another release may need adaptation. |
| [`.gitlab-ci.yml`](../.gitlab-ci.yml), [`tools/plugins/`](../tools/plugins/) | Course grading integration and Lean/import checks | Useful clues about expectations; the complete grading environment is not included. |

The grading plugin expects task-specific `Check.lean` files, which are absent from this checkout. It also rejects the exact broad import `import Mathlib`. Several starters use that import initially and end with `#min_imports`, inviting you to replace it after completing the proof. Local checking is useful, but does not reproduce the private grading system.

## The order to attack the material

Follow this dependency order:

**Setup → propositional logic → quantifiers and equality → natural-number induction → functions → sets → inductive data and binary trees → structures and type classes → filters and limits → finite sums and series → irrationality of `e` → derivatives and Newton convergence → measure/integration survey → independent formalization and audit.**

Within lecture group 2, start with `lecture_2_functions.lean`: it introduces arrow types, functions, lambdas, partial application, and universes. Then use `lecture_2_sets.lean` for the sets assignment and `lecture_2_types.lean` for structures and recursive data. Bring forward its short structures section if a function or set example needs it.

Split `lecture_1_induction.lean` into two sittings: lines 1–192 cover quantifiers, rewriting, and simplification; lines 193–351 cover induction and recursion. Split the 834-line analysis lecture into its actual sections. Read sums before derivatives for this plan, because that prepares you for `SqrtSum` and `IrrationalE`. Revisit derivatives immediately before Newton.

The analysis sequence is a recommendation based on prerequisites and scaffolding. File length and the printed score are poor workload estimates: Newton has one 100-point theorem and almost no intermediate scaffolding; `IrrationalE` provides six graded theorem statements and hints.

## The 28-study-week plan and book crosswalk

Dates assume study week 1 begins **Monday, 26 October 2026**. Each unit takes two study weeks, about 6–8 hours total. The suggested final deadline is **Friday, 21 May 2027, at 5 p.m., America/Chicago**. This is 28 study weeks spread across 30 calendar weeks, including a planned break **21 December 2026–3 January 2027**. Other unit deadlines below are also Fridays at 5 p.m. Do not compress the difficult analysis assignments to recover a date.

In the table, **read** means work through the relevant explanations and run examples; **survey** means understand the vocabulary and one example. Spread each row's reading across its two weeks. Start with two or three representative book exercises per unit, adding more only if an independent checkpoint exposes a gap. These are selected readings, not an assignment to complete every exercise in both books. Homework takes priority over extra book exercises.

| Unit / study weeks / due | Course material and homework | Companion reading | Evidence required |
| --- | --- | --- | --- |
| **1 · weeks 1–2 · Nov 6** | Setup; `lecture_1_prop_logic.lean`; Hello and Propositional homework | MIL ch. 1, §§3.3–3.5. TPiL ch. 1, §§2.1–2.4, ch. 3; consult ch. 5 basic tactics. | Both homework files complete in your practice copies; explain a short proof as a term and as a tactic proof. Identify the deliberately false introductory statement in the lecture. |
| **2 · weeks 3–4 · Nov 20** | `lecture_1_induction.lean`, lines 1–192; Quantifiers homework | MIL §§2.1, 2.3–2.4, 3.1–3.2. TPiL ch. 4 and ch. 5 rewriting/simplifier sections. | Quantifiers complete; produce a witness, unpack an existential hypothesis, and explain why quantifier order matters. |
| **3 · weeks 5–6 · Dec 4** | Remaining induction lecture; all four Induction homework theorems | MIL §§5.2, 5.4. TPiL §8.3, §8.5; preview natural-number constructors in ch. 7. | Induction complete; explain ordinary versus strong induction and why a variable sometimes needs generalizing. Pass checkpoint A. |
| **4 · weeks 7–8 · Dec 18** | `lecture_2_functions.lean`; Functions homework | MIL §4.2. TPiL §§2.5–2.9 and ch. 6 messages/imports/namespaces/library use. | Functions complete, including the definitions and all three counterexample checks; use function extensionality. |
| **5 · weeks 9–10 · Jan 15** | `lecture_2_sets.lean`; Set homework | MIL §4.1. TPiL revisit ch. 4 equality and ch. 5. | Set complete; distinguish a set from a type; prove set equality by membership and formalize an explicit counterexample. |
| **6 · weeks 11–12 · Jan 29** | `lecture_2_types.lean`; BinTree homework | MIL §6.3 and §7.1. TPiL ch. 7 and §§8.1–8.3; survey §§8.6–8.10. | BinTree complete, including `add`; explain structural recursion, the induction hypotheses, and the midpoint case in `reverse_eval`. |
| **7 · weeks 13–14 · Feb 12** | Analysis lecture, lines 1–251: structures, class instances, hierarchy, compactness example | MIL §§2.2, 2.5, 7.2, 8.1; survey §§8.2–8.3. TPiL chs. 9–10 and relevant ch. 6 options/attributes. | Build one small class/instance example; find and apply a theorem with inferred instance arguments; read an extreme-value theorem's hypotheses. Pass checkpoint B. |
| **8 · weeks 15–16 · Feb 26** | Analysis lecture, lines 253–480: filters, limits, eventual statements, continuity | MIL §3.6 and §§11.1–11.2; survey §11.3. | Prove one elementary sequence limit from an epsilon argument and another by composing library lemmas; explain `Eventually`, filter order, `NeBot`, and Hausdorff assumptions. |
| **9 · weeks 17–18 · Mar 12** | Analysis lecture, lines 562–678: finite sums and series; SqrtSum homework | MIL §§6.1–6.2; course lecture supplies the series material. | Both SqrtSum theorems complete; handle casts, finite intervals, and the term at zero. Distinguish a sum expression from a convergence theorem. |
| **10 · weeks 19–20 · Mar 26** | IrrationalE homework: five preparatory theorems, through `factorial_mul_sum_int` | MIL §5.1 for divisibility/cast practice; inspect the specific Mathlib lemma signatures named in the homework. | All five helpers complete and checked individually; record their dependency order. The final theorem remains the next unit's task. |
| **11 · weeks 21–22 · Apr 9** | Complete `exp_one_irrational`; analysis lecture, lines 481–561: derivatives | MIL §12.1; survey §12.2. | IrrationalE complete, with its dependencies; prove a simple derivative example and read a mean-value/monotonicity lemma. Pass checkpoint C. |
| **12 · weeks 23–24 · Apr 23** | Newton homework, first pass | Revisit MIL §11.1 and §12.1; search local Mathlib for the specific convexity, monotonicity, and convergence lemmas needed. | Write a complete paper proof for the exact stated hypotheses; formalize the recurrence and at least two useful auxiliary lemmas. Do not count the final theorem as complete yet. |
| **13 · weeks 25–26 · May 7** | Finish Newton; analysis lecture, lines 682–834: measure and integration | MIL §13.1; survey §§13.2–13.3 and the lecture's Bochner construction. | Newton complete; check a simple interval integral and combine two almost-everywhere statements. Explain measurability and integrability hypotheses. Deep Bochner implementation is a later specialization. |
| **14 · weeks 27–28 · May 21** | Independent mini-project, cumulative review, and proof audit | TPiL ch. 11 and ch. 12 in full; revisit remaining needed parts of chs. 5–6. | A small formalization with 2–4 supporting lemmas, a checked final theorem, a statement/axiom audit, and a replay command. Pass checkpoint D. |

The winter break is already included in these dates: study week 9 starts on 4 January. The [tracker](Progress.md) has a row for every active week and lets you write adjusted deadlines. If a unit needs a third week, move the later deadlines; keep the prerequisite order. Reestimate after the first two units using the time your actual proofs required.

This plan budgets about 84–112 active hours. If you later increase to **6–8 hours/week**, each two-week unit can often become one week, for about 14 study weeks. The current plan uses your 3–4-hour budget throughout. These are workload estimates; difficult assignments and newly released material can extend them. Two independent sessions and a later reconstruction matter more than maximizing speed.

### The first and second week of each unit

The first week must produce a small checked result, not just preparation. Use the second week for the remaining work and a delayed reconstruction.

| Unit | First week's Friday milestone | Second week's Friday milestone |
| --- | --- | --- |
| 1 | Setup check, Hello complete, two reconstructed logic examples | All three Propositional theorems |
| 2 | `exists_not_of_not_forall` and a checked rewriting example | `func_equation`; Quantifiers complete |
| 3 | Strong-induction and least-element theorems | The other two Induction theorems; checkpoint A |
| 4 | Injective composition and the fully checked counterexample | Surjective cancellation and the surjection from naturals to integers |
| 5 | Convex intersection and the union counterexample | `subset_even`; Set complete |
| 6 | Read the data definitions; prove `reverse_reverse` | `reverse_eval`, `add`, and `add_eval`; BinTree complete |
| 7 | A small structure/class and one working instance | Generic theorem use and checkpoint B |
| 8 | Filter vocabulary and one epsilon-based limit | A compositional limit and an eventual statement |
| 9 | A finite-sum warm-up and the partial-sum lower bound | The divergence theorem; SqrtSum complete |
| 10 | First two IrrationalE helpers and a paper outline of the tail bounds | The other three helpers |
| 11 | `exp_one_irrational` with its complete dependencies | Derivative example and checkpoint C |
| 12 | Exact Newton paper argument and one checked auxiliary lemma | Recurrence checks and a second useful auxiliary lemma |
| 13 | `newton_tendsto` complete | Interval-integral and almost-everywhere examples |
| 14 | Mini-project definitions/lemmas; foundations reading | Main theorem, audit, replay, and checkpoint D |

## How to use each week

Reserve recurring blocks you can actually protect. A three-and-a-half-hour pattern uses four weekdays:

| Session | Time | What to do |
| --- | --- | --- |
| Monday | 50 min | Preview the assignment for 5 minutes, watch about 30 minutes of the relevant video, then reconstruct one example for 15 minutes with the video closed. |
| Tuesday | 60 min | Main homework attempt. Write the mathematical proof before reaching for tactics. |
| Thursday | 60 min | Continue the proof or finish the week's named milestone; search for lemmas after identifying their required statement. |
| Friday | 40 min | About 20 minutes of targeted MIL/TPiL work, then checking, a short delayed reconstruction, and the tracker. |

An optional 30-minute session brings the total to four hours. The blocks are suggestions, not calendar events. If a recording is longer than the input block, split it at a mathematical boundary and continue in the next input session. A lecture group can span several weeks. Do not add an entire extra video on top of an already full week. If a book section needs more time, use the next Monday's input block rather than exceeding the budget.

After a video segment, close the solution and reproduce **one example, explain one definition, and attempt one variant**. Take notes about a concept, an error, and a useful lemma; do not transcribe the recording. The book should resolve an obstacle or supply an exercise, rather than become a second passive lecture.

### When stuck

Work independently for about 25 minutes. Then classify the blockage: mathematical argument, missing library lemma, type/coercion mismatch, or tactic syntax. Write the exact goal and the statement of the lemma you wish existed. Spend another 10–15 minutes using `#check`, go-to-definition, local search, or a relevant book example.

If still stuck, ask for **one hint or a matching lemma**, including the minimal code, goal state, attempted step, and Lean version. After two serious sessions with no progress, get targeted help instead of repeatedly guessing tactics. Record the help and rebuild that portion unaided 48–72 hours later. A correct proof obtained with help is useful practice; it becomes independent mastery after you can reconstruct and explain it.

For propositional and quantifier homework, obey the exact tactic lists in the starter files. In Induction, `grind` is forbidden and `omega` is explicitly permitted. On later assignments, use automation after you know the argument and can explain its hypotheses. Do not close a homework by invoking the same library theorem that the exercise asks you to establish; supporting Mathlib lemmas are expected.

## How to work without changing the course files

The course files remain reference copies. During your own study sessions, create a practice copy of the homework tree under this new folder. The following commands are **instructions for later use**; setup, copying, dependency downloads, and Lean builds have not been run as part of preparing this guide.

From the repository root, run the copy step once:

```sh
mkdir -p SelfStudy/Practice
cp -R Shad/Homework SelfStudy/Practice/Homework
```

This creates the practice tree. If it already exists, open it rather than repeating the recursive copy. Keep lecture experiments in separate files in `SelfStudy/Practice/`, with a fresh namespace for each experiment. Copy selected definitions/examples; importing entire lecture files can bring in deliberate errors and extra axioms.

The repository's own setup instructions use these commands separately:

```sh
lake exe cache get
lake build
lake env lean Test.lean
```

The first obtains compiled dependencies and can take substantial disk space (the course README estimates about 6 GB). `lake build` prepares the project's configured targets. `lake env lean Test.lean` should report the type of `TopologicalSpace` without errors. A successful project build does **not** certify completion of all homework, especially files that the root does not import.

After you have created and worked on a practice copy, check that exact file:

```sh
lake env lean SelfStudy/Practice/Homework/Logic/Propositional/Propositional.lean
```

Lean may succeed while warning about `sorry`. Inspect the messages. For a preliminary source scan of that file:

```sh
rg -n '\b(sorry|admit|axiom)\b' SelfStudy/Practice/Homework/Logic/Propositional/Propositional.lean
```

A scan with no matches normally prints nothing. Matches in comments are possible; a scan is only a preliminary check, not a dependency audit. Use `#check`, `#print`, and `#print axioms` for **each named theorem you are claiming as finished** in the working file. Anonymous `example`s need their own source review or a name if you want to inspect their dependencies.

Keep MIL's exercises in its own project with its own pins if a copied exercise does not fit the course environment. MIL's introduction explicitly recommends working in a copy of its exercise directory. The online MIL pages currently label themselves `v4.19.0`; the TPiL landing page names Lean `4.33.0`, while this course pins `4.33.1`. These labels indicate that exact APIs may differ; they do not by themselves establish incompatibility. Prefer local go-to-definition and the repository's pinned dependencies when solving the course homework. Do not upgrade the course simply to match a webpage.

## What counts as verified, and what counts as learned

There are three separate questions: **Did Lean check this statement? Is this the intended mathematical statement? Can you explain and reconstruct the proof?** Your study process should answer all three.

The lecture files illustrate why this distinction matters. `lecture_2_sets.lean` contains `axiom bad : 2 + 2 = 5` and an unfinished theorem of `False`. In `lecture_1_prop_logic.lean`, the introductory `fermat_last` statement omits restrictions needed even to exclude zero solutions and is filled with `sorry`. For example, setting all three variables to zero defeats its displayed conclusion. These are teaching material to analyze, not finished results to trust or import wholesale.

A finished assignment must have the exact intended statement and all required definitions, every claimed proof and supporting dependency complete, no unchecked placeholder dependencies, and the exercise's restrictions respected. Run `#print axioms theoremName`: `sorryAx` marks a gap, and an unexpected custom axiom needs investigation. Ordinary mathematical Lean proofs can legitimately depend on `propext`, `Classical.choice`, and `Quot.sound`; an empty axiom list is not the general completion criterion. This audit is a necessary part of the workflow, not a claim that you have independently audited the kernel implementation.

When checking statements, pay particular attention to:

- Vacuity: contradictory assumptions, empty types/sets, or accidental extra hypotheses.
- Quantifiers and domains: `ℕ` versus `ℤ` versus `ℝ`, nonzero assumptions, bounds, and casts.
- Equality: definitional reduction (`rfl`), a theorem of equality, function/set extensionality, and proposition equivalence.
- Total definitions: real division is defined at zero; `deriv` has a default at non-differentiable points; a real-valued `tsum` expression alone does not assert summability; the Bochner integral alone does not assert integrability.
- The default `HasSum`/`Summable` notion used in the lecture is unconditional. Do not silently identify it with convergence of arbitrary ordered partial sums.
- Newton's exact hypotheses: the starter allows arbitrary `x₀`. Do not add an initial-side assumption or extra smoothness simply to make your proof work.

### Four independent checkpoints

**A, after study week 6:** Across a 60-minute proof block and, if needed, a 30-minute flex block, solve six short unfamiliar variations: implication, a conjunction/disjunction, an existential, a rewrite, ordinary induction, and strong induction or a least-element argument. Use the assignment's elementary restrictions where relevant. Require all six eventually; if fewer than five succeed in 60–90 minutes, spend another week on the foundations before advancing. This is a suggested diagnostic threshold. It replaces that week's normal practice; it is not extra work above the budget.

**B, after study week 14:** Without a tutorial, define a small recursive function, prove a structural invariant, prove a function or set extensional equality, and explain one successful instance synthesis. Check the resulting theorem dependencies. Select the mini-project topic now. Use a normal proof session for this assessment.

**C, after study week 22:** Prove a new elementary limit, a comparison/summability variation, and a finite-sum identity with ordinary documentation and library search. Explain one successful and one unsuccessful theorem application by reading the hypotheses. Every item should eventually check; a copied finished homework is not this checkpoint. Spread it across the normal proof sessions if needed.

**D, study week 28:** Present a 10-minute explanation of a small formalization, starting with the exact informal statement and ending with the checked theorem, assumptions, dependencies, and replay instructions. Another person should be able to check the code in the pinned environment. If working alone, perform the review in a fresh session a few days later.

A suitable mini-project for your geometry interests is **finite intersections of convex subsets of the plane**, extending the homework's explicit convexity definition. Bound the deliverable to a definition, 2–4 supporting lemmas, a main theorem, and boundary cases such as an empty indexing family. A finite counting lemma is another good choice. Use familiar mathematics; the new skill being tested is managing a complete formalization. This is a first working level of competence, with further practice needed for research-scale formalization.

## Accountability without enrollment

Choose an external deliverable: every Friday, have **one checked file or a precisely stated partial milestone** ready to show. The milestone for a long assignment is its named auxiliary lemmas, not “watched a lecture” or “worked for two hours.”

Use [Progress.md](Progress.md) for a two-minute weekly record: evidence, independent reconstruction, blocker, next action. Arrange a brief fortnightly review with a willing peer, or record a five-minute explanation for your own later review. The plan does not assume you can submit to the course's official grading service. No messages, calendar events, or reminders have been sent or created.

Use a small commitment rule: begin at the reserved time, work for 20 minutes, and write the next exact proof step before stopping. If a week collapses, do two 25-minute sessions that preserve contact with the current proof; leave the week's milestone incomplete and move the deadline. If you miss two weeks, resume the next incomplete prerequisite rather than restarting the books. Keep at most one primary unfinished homework at a time.

The incentives should support the work you care about: by study week 10 you will have formalized a convexity argument; by study week 28 you will have a small mathematical artifact you can explain and independently recheck.

## Extensions and keeping the syllabus current

**Optional study weeks 29–32:** Complete both statements in `Bonus/Cantor/Cantor.lean`. Allow about a week for Cantor's diagonal argument, then up to three for Cantor–Bernstein. MIL §4.3 is directly relevant, but contains an approach/solution: attempt the theorem independently before reading it. Label any reconstruction done after reading a solution. Reading readiness occurs after unit 5 (study week 10); scheduling the longer bonus after the core prevents it from delaying analysis.

**Next cycle, 4–8 weeks depending on scope:** Choose a mathematical direction. For discrete geometry, MIL ch. 6 and ch. 10 (linear algebra) are natural next targets. MIL ch. 9 treats groups and rings; §7.3 builds Gaussian integers. These are valuable extensions, not prerequisites for completing this repository's current assignments. Deeper MIL §§11.3, 12.2, 13.2–13.3 support further analysis work. Metaprogramming, large automated proof search, and verification of substantial software systems are later topics, beyond this course snapshot.

At Friday review, spend five minutes checking the [upstream repository](https://github.com/vasnesterov/public-2026-fall) for newly released files. New numbered lectures/homework belong after their prerequisites and before the final cumulative assessment. Add a row to the tracker and a concept to the checklist if necessary. Reestimate workload; do not silently squeeze another assignment into an already full week. No future course topics or video sequence have been invented here.

## Sources and verification status

Repository-specific statements come from the local files linked above and the [upstream snapshot](https://github.com/vasnesterov/public-2026-fall/commit/381add80c4008c04b487e3660d06eedf014a7d2e). Book links were checked on 21 October 2026. The study order, workload estimates, diagnostic thresholds, and suggested deadlines are recommendations.

- [MIL introduction and interactive exercise workflow](https://leanprover-community.github.io/mathematics_in_lean/C01_Introduction.html).
- [MIL chapter index](https://leanprover-community.github.io/mathematics_in_lean/), [logic](https://leanprover-community.github.io/mathematics_in_lean/C03_Logic.html), [elementary number theory](https://leanprover-community.github.io/mathematics_in_lean/C05_Elementary_Number_Theory.html), [discrete mathematics](https://leanprover-community.github.io/mathematics_in_lean/C06_Discrete_Mathematics.html), [structures](https://leanprover-community.github.io/mathematics_in_lean/C07_Structures.html), and [hierarchies](https://leanprover-community.github.io/mathematics_in_lean/C08_Hierarchies.html).
- [MIL basics](https://leanprover-community.github.io/mathematics_in_lean/C02_Basics.html) and [sets and functions](https://leanprover-community.github.io/mathematics_in_lean/C04_Sets_and_Functions.html).
- [MIL topology](https://leanprover-community.github.io/mathematics_in_lean/C11_Topology.html), [differential calculus](https://leanprover-community.github.io/mathematics_in_lean/C12_Differential_Calculus.html), and [integration and measure theory](https://leanprover-community.github.io/mathematics_in_lean/C13_Integration_and_Measure_Theory.html).
- [TPiL chapter index](https://lean-lang.org/theorem_proving_in_lean4/), [dependent type theory](https://lean-lang.org/theorem_proving_in_lean4/Dependent-Type-Theory/), [inductive types](https://lean-lang.org/theorem_proving_in_lean4/Inductive-Types/), [induction and recursion](https://lean-lang.org/theorem_proving_in_lean4/Induction-and-Recursion/), [type classes](https://lean-lang.org/theorem_proving_in_lean4/Type-Classes/), and [axioms and computation](https://lean-lang.org/theorem_proving_in_lean4/Axioms-and-Computation/).

The guide and printable artifact were checked as documents. The course's Lean dependencies are absent from `.lake` in this checkout, so no course build, homework compilation, or grading run was performed when preparing this plan.

The PDF is generated from [Syllabus.md](Syllabus.md) by [tools/build_syllabus.py](tools/build_syllabus.py). With ReportLab and DejaVu fonts available, regenerate it from the repository root with `python3 SelfStudy/tools/build_syllabus.py`.
