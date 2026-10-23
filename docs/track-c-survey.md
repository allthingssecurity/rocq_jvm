# Track C survey: machine-checked JVM concurrency and Java Memory Model work

Status: written 2026-10-23 for the `rocq-jvm` project (Rocq 9.3, Apache-2.0-compatible).
Scope: existing formalisations of Java/JVM threads and of the Java Memory Model
(JMM, JLS §17.4) that we might port, reuse, or use as a reference.

**How licences were checked.** Licences were checked only where I could read a licence
file or an official metadata field. This sandbox cannot reach `isa-afp.org` downloads,
Bitbucket, or the ACL2 GitHub tree directly (proxy or robots refusals). Where I could not
read the licence text, I say **unknown** and do not guess. Before anything is
copied, someone with full network access should re-check every "port" verdict
against the actual LICENSE file.

---

## 1. Summary table

| Work | Prover (version) | JMM / threads content | Licence (verified?) | Maintained? | Verdict |
|---|---|---|---|---|---|
| JinjaThreads (Lochbihler) | Isabelle/HOL (AFP, current for Isabelle2025-2) | Interleaving semantics, locks, wait/notify, spawn/join, interrupts for source and bytecode; full JLS 17.4 JMM with justification/commit sequences; DRF guarantee; consistency; JMM type safety | BSD (AFP entry metadata says "BSD License"; LICENSE file not downloaded) | Yes. Updated with every AFP release | **Main reference.** Port definitions and proof structure by hand, not mechanically |
| Jinja (Klein & Nipkow) | Isabelle/HOL (AFP, Isabelle2025-2) | Sequential source, JVM and BCV only; no threads | BSD (AFP metadata) | Yes | Reference for Track A only |
| Aspinall & Ševčík, TPHOLs 2007 | Isabelle/Isar (~4000 lines, 2007) | JLS 17.4 legality, DRF guarantee for finite executions, list of JLS bugs | unknown (scripts were at a request URL I could not verify) | No (2007) | Reference: paper and bug list |
| Ševčík thesis / ECOOP 2008 (transformations) | Paper proofs (I found no mechanisation I could verify) | Which compiler transformations the JMM allows | n/a (thesis © Univ. Edinburgh) | No | Reference for the later causality model |
| Huisman & Petri, JMM in Coq (VAMP 2007) and BicolanoMT (Bytecode 2008) | Coq (2007/08 era) | Interleaving extension of Bicolano; partial JMM with DRF not finished; uses axioms | unknown (sites unreachable) | No | Ignore, beyond citing it |
| Bicolano (MOBIUS) | Coq (≈8.1, 2006–08) | Sequential CLDC bytecode | unknown (`mobius.inria.fr` unreachable) | No | Ignore for C (Track A may look at it) |
| CoqJVM (Atkey) | Coq 8.2pl1 (forks note 8.5rc1) | Executable sequential JVM with dependent types; no threads | unknown: no LICENSE in either GitHub repo, so by default no rights are granted | No | Ignore for C |
| JAM (Bender & Palsberg, OOPSLA 2019) | Coq (2019) + Herd `cat` model | Axiomatic model of VarHandle modes (plain, opaque, RA, volatile) and fences; DRF-SC; monotonicity | unknown (Zenodo lists a LICENSE.md I could not read) | No (one-off artifact) | Reference. Good target for a later model with access modes |
| Promising 1/2 (Kang, Hur, Lahav, Vafeiadis, Dreyer; Lee et al.) | Coq/Rocq (README: Rocq 9.0+) | C11-style promising semantics; DRF-PF; local DRF-PF/RA/SC in `promising-ldrf-coq` | MIT (repo metadata, LICENSE.md) | Yes | Reference. Proof techniques only (not Java) |
| IMM (Podkopaev, Lahav, Vafeiadis) | Coq (Nix pinned) | Intermediate model, compilation proofs to TSO/POWER/ARM | MIT (repo metadata) | Yes | Reference. Later JMM-to-hardware work |
| hahn (Vafeiadis) | Coq (README: 8.15; packaged as `coq-hahn`) | Relation library: acyclicity, closures, rewriting tactics | MIT ("Copyright (c) 2016 Viktor Vafeiadis", LICENSE read) | Yes | Candidate to vendor later. Not used now (stdlib-only rule) |
| Plan B / BMM (Demange, Laporte, Zhao, Pichardie, Jagannathan, Vitek, POPL 2013) | Coq definitions and statements; proofs on paper | Buffered (TSO-like) Java model, ⊂ JMM; DRF | unknown | No | Reference |
| CompCertTSO (Ševčík et al.) | Coq 8.3pl1 | x86-TSO compiler for a C-like language; not Java | unknown (a LICENSE file exists but I could not read it; it derives from CompCert, so assume a non-commercial INRIA-style licence until verified) | No | Ignore (licence risk, not Java) |
| K-Java (Bogdanas & Roşu, POPL 2015) | K framework | Java source semantics; threads are used for model checking; no JMM that I could confirm | unknown (no licence shown on `kframework/java-semantics`) | Low activity | Reference for test suites only |
| JavaFAN (Farzan, Chen, Meseguer, Roşu, CAV 2004) | Maude | Java and JVM rewriting semantics, interleaving | unknown | No | Ignore |
| M6 (Hanbing Liu & J Moore, ACL2) | ACL2 | CLDC JVM with threads and monitors (interleaving; no JMM) | unknown (ACL2 community books; per-file headers not checked) | No | Reference for monitor/thread-table design (Track A) |
| Lean | None found | I found no JVM or JMM formalisation in Lean 4 | n/a | n/a | n/a |
| jMT (Panneke & Wehrheim, 2026) | Testing tool, not a prover | Executes candidate Java memory models on 169 litmus tests | unknown | New | Useful later as a litmus oracle |

---

## 2. Details

### 2.1 JinjaThreads and Jinja (Lochbihler; Klein & Nipkow): Isabelle AFP

* Sources: <https://www.isa-afp.org/entries/JinjaThreads.html> (download
  `https://isa-afp.org/release/afp-JinjaThreads-current.tar.gz`), session theory list
  at <https://www.isa-afp.org/sessions/jinjathreads/>; Jinja at
  <https://www.isa-afp.org/entries/Jinja.html>.
* Papers: Lochbihler, *Java and the Java Memory Model: a Unified, Machine-Checked
  Formalisation*, ESOP 2012; *Making the Java Memory Model Safe*, ACM TOPLAS 35(4), 2014
  (<https://i44vm2.informatik.kit.edu/uploads/publikationen/lochbihler14toplas.pdf>);
  also FOOL 2008, ESOP 2010, ITP 2011.
* Coverage:
  * A generic interleaving framework (`FWState`, `FWLocking`, `FWThread`, `FWWait`,
    `FWInterrupt`, `FWSemantics`, ...). The thread-local semantics is a parameter whose
    steps emit thread actions (new thread, lock, unlock, join, wait/notify, interrupt)
    and observable events. This is the same architecture we use for Track C.
  * The memory-model block (`MM`, `SC`, `JMM_Spec`, `JMM_DRF`, `SC_Completion`,
    `HB_Completion`, `Non_Speculative`, `JMM_Framework`, `DRF_J`, `DRF_JVM`, `JMM_Typesafe`, ...).
    It covers JLS 17.4 legality with justifying executions and commit sequences
    (rules L1–L9), and Aspinall–Ševčík's "weak legality" variant.
* Main theorems (TOPLAS 2014):
  * DRF guarantee, unconditional, using a corecursive construction of SC completions.
  * Consistency: every SC execution is legal (the first proof of this).
  * Type safety of the JMM when type information is stored in addresses.
* Faithfulness findings:
  * JMM pointer forgery: out-of-thin-air reference values break type safety when types
    are stored in objects, and the security architecture with either design.
  * Problems with initialisation and allocation, start synchronisation, and event
    identity across executions.
  * Rule 8 is dropped for infinite executions.
* Race definition: conflicting accesses exclude volatile locations. Lochbihler
  follows Jacobs's fix so that the guarantee also covers programs that
  synchronise through volatiles. We adopt this definition.
* Licence: the AFP "About" page says entries are BSD-style or LGPL. The entry pages for
  both JinjaThreads and Jinja say **"BSD License"**. BSD is Apache-2.0-compatible, so a
  hand port with attribution is fine. I could not open the LICENSE file itself.
* Maintenance: active (there is an Isabelle2025-2 release dated 2026-02-06).
* Verdict: **use as the primary reference, and port by hand**. Isabelle/HOL is
  classical and relies on locales, coinduction and the Collections Framework, so a
  mechanical translation is not realistic. We copy the design and lemma structure:
  * SC completions
  * hb-consistency
  * `Non_Speculative`, needed later for the commit model
  * the race definition

### 2.2 Aspinall & Ševčík, *Formalising Java's Data Race Free Guarantee* (TPHOLs 2007)

* Paper: <https://homepages.inf.ed.ac.uk/da/papers/drfformalization/drfformalization.pdf>;
  report EDI-INF-RR-0958 <https://www.inf.ed.ac.uk/publications/report/0958.html>.
* Prover: Isabelle/Isar, about 4000 lines. Scripts were said to be at
  `http://groups.inf.ed.ac.uk/request/jmmtheory/` (I did not verify this URL).
* Content: JLS 17.4 legality over finite executions. Theorem 1: "any legal execution
  of a well-formed data race free program is sequentially consistent."
* JLS problems found:
  * Initialisation writes are not synchronisation actions, yet they are said to
    synchronise-with every thread.
  * Infinitely many volatile initialisations break the ω-order of `so`.
  * The JLS's SC definition ignores mutual exclusion.
  * The hb-consistency condition omits `W(r) = w`.
  * Causality tests 17–20 fail.
  * The original proof of Lemma 2 is wrong.
* The DRF proof does not use legality rules 1, 3, 4, 8 or 9.
* Licence: unknown. Maintenance: none.
* Verdict: **reference**. The bug list is a checklist for our definitions. Its rule
  analysis tells us which parts of the commit model DRF needs, and it says the hard
  part is ruling out thin-air values.

### 2.3 Ševčík: program transformations in the JMM

* Ševčík & Aspinall, *On Validity of Program Transformations in the Java Memory
  Model*, ECOOP 2008 (doi:10.1007/978-3-540-70592-5_3).
* Ševčík, PhD thesis, *Program Transformations in Weak Memory Models*, Edinburgh 2009
  (<https://era.ed.ac.uk/handle/1842/3132>).
* Results:
  * Eliminating overwritten writes and reordering independent accesses are valid.
  * Common subexpression elimination is invalid.
  * Several HotSpot optimisations are unsound with respect to the JMM.
* Mechanisation: I found none I could verify.
* Verdict: **reference** for later work. This is why we must not claim that
  HotSpot-compiled code satisfies the full JMM. The JMM itself is unsound for some
  real optimisations.

### 2.4 Bicolano, BicolanoMT and Huisman–Petri JMM (MOBIUS, Coq)

* MOBIUS deliverables D3.1/D3.3
  (<https://software.imdea.org/~gbarthe/mobius/bin/view/DeliverablesList/D3.3.pdf>).
  * Bicolano is a sequential CLDC bytecode semantics in Coq.
  * BicolanoMT adds interleaving, with some multithreaded instructions missing.
  * The Coq JMM covers finite executions only, has no thread creation or termination,
    and assumes several axioms (sequential continuation, topological sort, first
    occurrence). D3.3 says the final DRF proof "was not yet written".
* Papers: Huisman & Petri, *The Java Memory Model: a Formal Explanation*, VAMP 2007;
  *BicolanoMT: a formalization of multi-threaded Java at bytecode level*, Bytecode 2008
  (ENTCS).
* Source: `http://mobius.inria.fr/bicolano` (could not be fetched). Licence: **unknown**.
  Coq version: about 8.1. Maintenance: dead.
* Verdict: **ignore** apart from citation. It is outdated Coq, has an unknown licence,
  and its JMM part is incomplete and relies on axioms.

### 2.5 CoqJVM (Atkey)

* <https://github.com/bobatkey/coqjvm> (fork of `bacam/coqjvm`);
  paper at <https://strathprints.strath.ac.uk/74424/> (TYPES 2007).
* An executable, dependently typed specification of a large sequential JVM
  fragment, with a resource verifier. It has no threads and no memory model.
* Coq 8.2pl1 (the fork README mentions 8.5rc1).
* Licence: **unknown**. Neither repository shows a LICENSE file, which by default means
  no rights are granted.
* Verdict: **ignore for C**. Track A could read it for ideas on class-file data structures.

### 2.6 Bender & Palsberg, *A Formalization of Java's Concurrent Access Modes* (OOPSLA 2019), JAM

* Paper: <https://par.nsf.gov/servlets/purl/10193297>.
  Artifact: <https://zenodo.org/records/3365412>
  (doi:10.5281/zenodo.3365412); repository `https://bitbucket.org/ucla-pls/jam/`
  (`coq/`, `herd/`).
* Coverage:
  * An axiomatic model of the JDK 9 VarHandle modes (plain, opaque,
    release/acquire, volatile), five fence kinds and RMWs, written in Herd `cat`.
  * Validated on litmus tests.
* Coq proofs:
  * monotonicity
  * irreflexive visibility
  * DRF-SC
  * "causal acquire reads"
* It rules out thin-air values with `acyclic(po ∪ rf)` restricted to opaque and
  stronger accesses. It does **not** model JLS 17.4 causality.
* Licence: **unknown** (Zenodo lists `LICENSE.md` but I could not read it).
* Verdict: **reference**. It is the natural next model after the JLS one, because
  Camel and its dependencies (e.g. `java.util.concurrent`) use VarHandles. Read it
  for the DRF-SC proof structure in Coq. Do not copy code until the licence is verified.

### 2.7 Promising semantics, IMM and hahn (Kang, Hur, Lahav, Vafeiadis, Dreyer, Podkopaev, Lee, Cho, ...)

* `snu-sf/promising-coq` (<https://github.com/snu-sf/promising-coq>)
  * Licence: **MIT** (LICENSE.md). README says Rocq 9.0+.
  * Formalises DRF-PF; it notes that DRF-RA and DRF-SC are not formalised there.
* `snu-sf/promising-ldrf-coq` (<https://github.com/snu-sf/promising-ldrf-coq>;
  PLDI 2021, *Modular data-race-freedom guarantees in the promising semantics*)
  * Licence: **MIT**. Rocq 9.0+.
  * Proves local DRF-PF, local DRF-RA and local DRF-SC (`src/ldrfsc/LocalDRFSC.v`).
* `weakmemory/imm` (<https://github.com/weakmemory/imm>)
  * Licence: **MIT**.
  * IMM, and compilation from IMM to TSO, POWER and ARMv8. Related repos:
    `promising2ToImm` (MIT), `promising1ToImm`.
* `weakmemory/hahn` (<https://github.com/weakmemory/hahn>)
  * Licence: **MIT** (LICENSE text read: "The MIT License (MIT) Copyright (c) 2016 Viktor Vafeiadis").
  * README targets Coq 8.15. The `coq-hahn` opam package is not installed in our switch.
  * A relation library: closures, acyclicity, path decompositions, `rewrite`-style relation algebra.
* Verdict:
  * Promising and IMM are **references** for proof technique (DRF via "first race"
    arguments, local DRF, compilation to hardware).
  * hahn is the best candidate if we later need a relation library. MIT is fine for
    Apache-2.0. **We do not vendor it now**:
    * the current development needs only `clos_trans` and a few lemmas;
    * the task restricts us to stdlib;
    * hahn's Rocq 9.3 compatibility is unverified.
  * Revisit when the commit-based model needs heavy relation algebra.

### 2.8 Other JMM work worth knowing

* **Plan B / BMM** (Demange et al., POPL 2013,
  <https://www.cs.purdue.edu/homes/suresh/papers/popl13.pdf>).
  * A TSO-like buffered model for Java that is a strict subset of the JMM.
  * Coq contains definitions and statements; the proofs are on paper.
  * Project page `http://r.cs.purdue.edu/bmm`. Licence unknown.
  * **Reference.**
* **Cooking the Books** (Petri, Vitek, Jagannathan, ECOOP 2015,
  <https://www.cs.purdue.edu/homes/suresh/papers/ecoop15.pdf>).
  * Formalises the JSR-133 cookbook recipes.
  * Finds that the POWER recipe conflicts with the JMM.
  * Paper proofs only. **Reference.**
* **Cenciarelli, Knapp, Sibilio**, *The Java Memory Model: Operationally,
  Denotationally, Axiomatically*, ESOP 2007.
  * Found the bug that Aspinall–Ševčík fixed.
  * Paper only. **Reference.**
* **jMT** (Panneke & Wehrheim, arXiv:2604.15978, 2026).
  * Executable checker of Java memory models against 169 litmus tests.
  * Not a prover. **Possible oracle** for Track B-style differential litmus testing.

### 2.9 K, Maude, ACL2, Lean

* **K-Java** (Bogdanas & Roşu, POPL 2015,
  <https://fsl.cs.illinois.edu/publications/bogdanas-rosu-2015-popl.html>;
  <https://github.com/kframework/java-semantics>).
  * Java *source* semantics, with model checking of multithreaded programs.
  * I could not confirm any JMM support. The repository wiki page on the memory
    model only gives background.
  * Licence not shown: **unknown**.
  * **Reference** (its conformance test suite).
* **JavaFAN** (Farzan, Chen, Meseguer, Roşu, CAV 2004; Maude).
  * Java and JVM semantics with interleaving, no memory model stated.
  * **Ignore.**
* **ACL2 M6** (Hanbing Liu's dissertation, J Moore,
  <https://cs.utexas.edu/~moore/publications/liu-dissertation.pdf>).
  * Executable CLDC JVM with thread table and monitors.
  * Interleaving only; the dissertation describes no memory model.
  * Lives in the ACL2 community books (`books/models/jvm/`). Licence of those files
    unknown (not checked).
  * **Reference** for Track A's monitor design.
* **Lean 4**: searches found no JVM or JMM formalisation.

---

## 3. Recommendation

### 3.1 Which memory model first

Your expectation was "SC interleaving + happens-before model + DRF-SC first".
I agree with it, with one correction that the formal development makes precise.

**The happens-before model alone (JLS §17.4.5 hb-consistency) does *not* satisfy
DRF-SC.** JLS §17.4.8 shows this with the program
`r1 = x; if (r1 != 0) y = 1;  ||  r2 = y; if (r2 != 0) x = 1;`:

* It is correctly synchronised: no SC execution writes anything, so no SC execution
  has a race.
* Yet the hb-consistent execution with `r1 = r2 = 1` is allowed. Each read sees a write
  that is not hb-after it.

This is the whole reason the JMM has the causality (commit) rules of §17.4.8.

So the first target is:

1. **SC interleaving semantics** over an abstract thread-local LTS.
2. **The hb model** (well-formedness §17.4.7, sw/hb §17.4.4–5, hb-consistency
   §17.4.5, so-consistency for volatiles §17.4.7(5)). We define it exactly.
3. Two theorems:
   * **(a) Per-execution DRF lemma.** A well-formed, hb-consistent execution that is
     itself race-free is SC. No extra assumptions are needed. This is the core lemma
     of every JMM DRF proof (Aspinall–Ševčík Lemma 2, Lochbihler's `JMM_DRF`).
   * **(b) Program-level DRF-SC for "hb + no-thin-air"**, meaning hb-consistency
     plus `acyclic(po ∪ so ∪ rf)`. This model is strictly *stronger* than the JMM: it
     forbids load buffering, which the JMM allows. So (b) does **not** imply DRF-SC
     for the JLS model.
4. **Next: the full JLS §17.4.8 commit model.** Following Lochbihler, prove that
   legal executions of DRF programs are SC via SC completions. Theorem (a) is reused
   unchanged there.
5. **Later: JAM-style access modes** (VarHandles) and final fields (§17.5).

### 3.2 Port versus write fresh

* **Write fresh, in plain Rocq stdlib.**
  * Events, executions, po/so/sw/hb, races, SC semantics, DRF proofs. This is a few
    hundred lines. None of the Coq candidates matches our setting:
    * Bicolano and CoqJVM have no usable concurrency.
    * JAM targets a different model and its licence is unknown.
    * Promising and IMM are C11-style.
  * Isabelle cannot be ported mechanically.
* **Port by hand from JinjaThreads (BSD).** Port the commit-sequence legality
  definitions, `Non_Speculative`, and the SC-completion DRF proof when we do §17.4.8.
  BSD needs attribution, which is compatible with Apache-2.0. Re-check the LICENSE
  file first.
* **Possibly vendor `hahn` (MIT)** later, for relation algebra. Record its licence in
  `docs/` if we do.
* **Do not copy anything** from these until their licences are verified:
  * CoqJVM (no licence)
  * Bicolano/BicolanoMT
  * JAM
  * CompCertTSO (probably non-commercial)
  * K-Java
  * M6

  Nothing I found is GPL. LGPL is possible for some AFP entries, but JinjaThreads
  and Jinja are BSD. CeCILL could not be confirmed for any of them.
