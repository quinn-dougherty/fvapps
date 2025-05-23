#import "@preview/touying:0.5.5": *
#import "@preview/clean-math-presentation:0.1.1": *

#show: clean-math-presentation-theme.with(
  config-info(
    title: [Proving the Coding Interview: A Benchmark for Formally Verified Code Generation],
    short-title: [Proving the Coding Interview],
    authors: (
      (name: "Quinn Dougherty", affiliation-id: 1),
      (name: "Ronak Mehta", affiliation-id: 2),
    ),
    author: "Quinn Dougherty",
    affiliations: (
      (id: 1, name: "Beneficial AI Foundation"),
      (id: 2, name: "Coordinal Research"),
    ),
    date: datetime(year: 2025, month: 5, day: 3),
  ),
  config-common(
    slide-level: 2,
    //handout: true,
    //show-notes-on-second-screen: right,
  ),
  progress-bar: true,
)

#title-slide(logo1: image("images/baif.svg", height: 4.5em))

// == Outline <touying:hidden>

// #components.adaptive-columns(outline(title: none))

= Introduction

#focus-slide[
  #image("images/hf.png")
]

= Motivation
#focus-slide[Motivation]

#slide(title: "FVAPPS: Formally Verified APPS")[
  - We want more proof certificates per synthetic LoC.
    #pause
  - Previously, APPS (@Hendrycks2021MeasuringCC) scraped "job interview" style coding puzzles to be completed by Python synthesis.
    #pause
  - In FVAPPS, we convert these *Python* problems to *Lean* problems, and state correctness theorems.
    #pause
  - FVAPPS ships 4715 questions, each consisting of a function definition and 2-5 theorems, with a curated subset of 1083 samples.
  #pause
  #image("images/hendrycks-et-al.png")
]

#slide(title: "Formal verification and proof assistants: quality assurance")[
  #table(
    columns: (auto, auto),
    inset: 10pt,
    align: horizon,
    table.header([*QA Process*], [*Blindspot*]),
    [Unit tests], [What did I forget to test?],
    [Fuzzing/property-based tests], [Cases are non-exhaustive],
    [Formal verification], [The "world-spec gap" (i.e. sidechannels)],
  )
  #pause
  Proof assistants accomplish this degree of assurance by _exploiting inductive structure_.
]
#slide(
  title: "Formal verification and proof assistants: compile time knowledge",
)[
  - Python is ruled by _runtime knowledge_: the absence of an initial error message is tiny evidence that your program is correct
  - A dependent type theory like Lean is ruled by _compiletime knowledge_: the absence of an error message is strong evidence that your program is correct.
]

#slide(
  title: "Formal verification and proof assistants: out with math, in with software",
)[
  - Most formal proof automation effort is invested into mathematics (i.e. MiniF2F)
  - Instead, we could focus on *software* to bring the assurances of type theory to the real world
  - This benchmark is a babystep in that direction
]

= Benchmark Generation
#focus-slide[
  Benchmark Generation
]

#slide(title: "Scaffold")[
  #table(
    columns: (auto, auto),
    inset: 10pt,
    align: horizon,
    image("images/fig3.png"),
    [
      - A _scaffold_ or _agent_ is an architecture involving LLM calls and observations (_tool use_).
      #pause
      - The simplest possible architecture, which is all we need, is a *loop*.
    ],
  )
]

#slide(title: "Benchmark Generation Pipeline")[
  #image("images/fig1.png")
]

#slide(title: "Example Sample")[
  #image("images/fig2.png")
]

#slide(title: "Theorems per sample")[
  #image("images/fig4.png")
]

= Baselines

#focus-slide[
  Baselines
]

#slide(title: "What did we test?")[
  - LLMs were given a loop scaffold similar to that in the generation.
  #pause
  - We measured Sonnet 3.5 (October 2024) and Gemini 1.5 Pro (retrieved November 2024)
  #pause
  - A human baseliner attempted one sample for 10 hours
]

#slide(title: "Model baselines")[
  #table(
    columns: (auto, auto),
    inset: 10pt,
    align: horizon,
    image("images/fig3.png"),
    [
      406 theorems were attempted across 101 randomly selected samples

      Each sample requires a function definition to be filled in before theorems can be attempted

      On these, Sonnet proved 30% and Gemini proved 18%
    ],
  )
]
#slide(title: "Model baselines")[
  #image("images/table2.png")
]
#slide(title: "Model baselines")[
  #table(
    columns: (auto, auto),
    inset: 10pt,
    align: horizon,
    image("images/fig7.png"),
    [
      Of the theorems that got eventually completed, roughly 20% of each model’s were done in zero or one iteration of the loop.
    ],
  )
]
#slide(title: "Model baselines")[
  #image("images/fig6.png")
]

= Future
#focus-slide[Future]

#slide(title: "Future")[
  - Quality control for *soundness* (no false positives) could be improved
  #pause
  - Harvesting property tests from the real world and turning them into Lean theorems (go from job interview code to real code)
]

#focus-slide[#image("images/qr.gif")]

#show: appendix

= References

#slide(title: "References")[
  #bibliography("refs.bib", title: none, style: "ieee")
]
