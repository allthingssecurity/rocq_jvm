# Kickoff brief for the Rocq JVM session (paste-free: start a new session and say "Read camel-lean/rocq-jvm/KICKOFF.md and do it")

Project: a formal semantics of the Java Virtual Machine in Rocq (Rocq 9.3.0, installed with `brew install rocq`; if `rocq`/`coqc` is not on PATH yet the install may still be finishing — wait for it, do not install another prover), used to prove properties of the compiled bytecode of Apache Camel methods for ALL inputs. Owner: Shashank Mohan Jain (GitHub allthingssecurity). Working directory: /Users/I074560/Downloads/experiments/camel-lean/rocq-jvm/.

Read first: PLAN.md in this directory (phases, checkpoints, "Schedule compression" with three parallel tracks) and /Users/I074560/Downloads/experiments/camel-lean/findings/r79-jbmc-pilot.md (bounded model checking results, limits, calibration targets).

Why: inspired by Anthropic's formal-verification article (Claude proved compiled RISC-V/x86 binaries in Rocq against fuzz-test specs using a formal machine model). We do the same for JVM bytecode, where no maintained Rocq model exists.

Scope (the user's decision): the WHOLE JVM, gradually — threads and the Java memory model, natives, the JDK library, reflection, class loading and invokedynamic are all in scope; the single-threaded core comes first. The user wants it faster than 10 weeks: run the three tracks of PLAN.md in parallel (A interpreter; B loader + differential harness + JDK models; C threads/JMM against an abstract event interface). Search for existing Rocq/Coq/Isabelle formalisations to reuse or port before writing from scratch (JVM: Bicolano, Jinja/JinjaThreads; JMM: published DRF-SC proofs); cite and check licences.

Non-negotiable checkpoints:
1. Every opcode follows JVMS chapter 6 exactly (int wraparound, idiv by zero and MIN/-1, shift masks, float NaN rules, exception order).
2. A loader turns real `.class` files (javac --release 17, from the exact Camel source at a recorded commit) into Rocq terms; proofs are about that bytecode, never a hand translation.
3. Differential testing every phase: random inputs through the extracted model and on HotSpot (JDK 21, ~/homebrew/opt/openjdk@21); compare results and exceptions; a mismatch is a model bug to fix before proving anything.
4. First calibration: camel-wal `TransactionLog.canUpdate`. On apache/camel main it has a known off-by-one/stale-layer bug (CAMEL-26088; fix branch camel-wal-update-after-roll-over on remote `fork` in /Users/I074560/Downloads/experiments/camel-lean/camel). The spec must be REFUTED on main's bytecode and PROVED on the fix's bytecode. Next: CaseInsensitiveMap put/remove/compact (branch camel-util-case-insensitive-map-removed-slots: prove it behaves like an ordered map with a bounded slot count for every operation sequence), then StringHelper/FileUtil/URISupport helpers.
5. A written trust base: Rocq kernel + model + loader + the list of axiomatised natives.

Resource rules (this Mac OOM-rebooted before; another session runs Camel Maven builds): at most 2 heavy jobs at once across this project; take /Users/I074560/Downloads/experiments/camel-lean/.mvn-lock (mkdir to take, rmdir to release) around any HotSpot run above 1 GB; JVMs -Xmx2g and niced; keep >= 15 GB disk free; at most 2 background agents; never git stash.

Hands off: apache/camel PRs, JIRA, mailing lists, the Camel batch files (camel-lean/scripts/keys-*, prs/, camel-lean/wt/). Read Camel sources and build `.class` files only in your own copies under rocq-jvm/.

Deliverables: a Rocq project under rocq-jvm/ that builds with dune or `rocq makefile`; rocq-jvm/STATUS.md per phase (what is proved, what is assumed, opcode coverage, differential-test counts); a short daily summary for the user; proofs of the Camel fixes above (citing them in PRs is the user's call).

Start: tracks A+B Phase 1 (ints/longs, stack, locals, branches, switches, loader for one method, extraction + differential harness, canUpdate calibration) and track C (JMM literature survey + abstract event model) as the second agent.
