# Formalizing Görtz-Wedhorn's Algebraic Geometry in Lean 4

[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-lightblue.svg)](https://opensource.org/licenses/Apache-2.0)
[![Lean 4](https://img.shields.io/badge/Lean-4.24.0-blue.svg)](https://leanprover-community.github.io/)
[![Mathlib](https://img.shields.io/badge/Mathlib-4.24.0-blue.svg)](https://github.com/leanprover-community/mathlib4)

A formalization project in **Lean 4** of selected results from Ulrich Görtz and Torsten Wedhorn's *"Algebraic Geometry I"* (2nd Edition). This repository serves as a portfolio demonstration of formal mathematics and proof verification capabilities in modern algebraic geometry.

## Project Overview

This project formalizes selected results from Ulrich Görtz and Torsten Wedhorn's *Algebraic Geometry I* (2nd Edition) using Lean 4. The work focuses on building foundational infrastructure in scheme theory and dimension theory, with the long-term objective of formalizing significant theorems such as Bézout's theorem or Zariski's Main Theorem.

### Reference and Methodology

- **Primary Source**: Ulrich Görtz and Torsten Wedhorn, *Algebraic Geometry I*, 2nd Edition
- **Current Focus**: Chapter 5 (Schemes) and topological Krull dimension theory
- **Long-term Goals**: Major theorems including Bézout's theorem, Zariski's Main Theorem, and cohomological results

### Current Progress

**Completed Formalizations:**
- **Lemma 5.7 (Görtz-Wedhorn)**: Complete formalization of fundamental topological Krull dimension properties
  - Dimension inequality for subspaces: `dim(Y) ≤ dim(X)`
  - Strict inequality for proper closed subsets of irreducible spaces
  - Dimension formula via open covers: `dim(X) = sup{dim(U_i)}`
  - Dimension formula via irreducible components: `dim(X) = sup{dim(Y)}`
  - Scheme dimension characterization via local rings: `dim(X) = sup{dim(O_{X,x})}`

**Supporting Infrastructure:**
- **Reduced closed subschemes**: Construction of the unique reduced closed subscheme structure on a given closed subset of a scheme, using vanishing ideal sheaves and radical constructions

**Code Statistics:**
- Total formalization: approximately 800 lines of Lean 4 code
- Main dimension theory file: 675 lines
- Scheme construction utilities: 133 lines

## Setup and Installation

### Prerequisites
- [Lean 4](https://leanprover-community.github.io/get_started.html) (version 4.24.0)
- [Lake](https://github.com/leanprover/lake) build system
- Git

### Quick Start
```bash
git clone https://github.com/ADA-Projects/Lean-AG.git
cd Lean-AG
lake exe cache get
lake build
```

## Repository Structure

```
Lean-AG/
├── GWchap5/                         # Main formalization directory
│   ├── gw_sect5-3.lean             # Topological Krull dimension theory (675 lines)
│   └── RedClosedSubscheme.lean   # Reduced closed subscheme construction (133 lines)
├── GWchap5.lean                    # Root module imports
├── lakefile.toml                   # Lake build configuration
├── lean-toolchain                  # Lean version specification
└── README.md                       # This file
```

### File Descriptions

- **[`GWchap5/gw_sect5-3.lean`](GWchap5/gw_sect5-3.lean)**: Core dimension theory formalization
  - Maps between irreducible closed sets induced by continuous functions
  - Dimension inequalities for embeddings and subspaces
  - Topological Krull dimension theory
  - Complete proof of Lemma 5.7 (Görtz-Wedhorn)
  - Scheme dimension characterization via local rings

- **[`GWchap5/RedClosedSubscheme.lean`](GWchap5/RedClosedSubscheme.lean)**: Scheme-theoretic constructions
  - Reduced closed subscheme construction for closed subsets
  - Proof that the construction yields a reduced scheme
  - Supporting infrastructure for scheme theory

- **[`lakefile.toml`](lakefile.toml)**: Lake build system configuration with Mathlib v4.24.0 dependencies
- **[`lean-toolchain`](lean-toolchain)**: Specifies Lean 4.24.0 for reproducible builds

## Formalized Theorems

### Lemma 5.7 (Görtz-Wedhorn)

This foundational lemma establishes basic properties of topological Krull dimension:

```lean
theorem thm_scheme_dim :
  (∀ (X : Type*) [TopologicalSpace X] (Y : Set X),
    topologicalKrullDim Y ≤ topologicalKrullDim X) ∧
  (∀ (X : Type*) [TopologicalSpace X] (Y : Set X),
    IsIrreducible (Set.univ : Set X) →
    topologicalKrullDim X ≠ ⊤ →
    IsClosed Y → Y ⊂ Set.univ → Y.Nonempty →
    topologicalKrullDim Y < topologicalKrullDim X) ∧
  (∀ (X : Type*) [TopologicalSpace X] (ι : Type*) (U : ι → Set X),
    (∀ i, IsOpen (U i)) → (⋃ i, U i = Set.univ) →
    topologicalKrullDim X = ⨆ i, topologicalKrullDim (U i)) ∧
  (∀ (X : Type*) [TopologicalSpace X],
    topologicalKrullDim X = ⨆ (Y ∈ irreducibleComponents X), topologicalKrullDim Y) ∧
  (∀ (X : Scheme), schemeDim X = ⨆ x : X, ringKrullDim (X.presheaf.stalk x))
```

### Supporting Results

**Maps on Irreducible Closed Sets:**
- `IrreducibleCloseds.mapOfContinuous`: Maps induced by continuous functions
- `mapOfContinuous_injective_of_embedding`: Injectivity for embeddings
- `mapOfContinuous_strictMono_of_embedding`: Strict monotonicity for embeddings

**Dimension Theory:**
- `topologicalKrullDim_subspace_le`: Dimension inequality for subspaces
- `topological_dim_proper_closed_subset_lt`: Strict inequality for proper closed subsets
- `topological_dim_open_cover`: Dimension via open covers
- `topological_dim_irreducible_components`: Dimension via irreducible components
- `scheme_dim_eq_sup_local_rings`: Scheme dimension via local ring dimensions

**Scheme Constructions:**
- `reducedClosedSubscheme`: Construction of reduced closed subschemes
- `reducedClosedSubscheme_ι`: Closed immersion from reduced subscheme
- `reducedClosedSubscheme_isReduced`: Proof that the construction is reduced

## Development Roadmap

### Near-term
- Complete fundamental results from Chapter 5
- Additional scheme-theoretic constructions and morphism properties

### Medium-term
- Intersection theory foundations
- Projective geometry and varieties
- Major theorems: Bézout's theorem, Zariski's Main Theorem

### Long-term
- Cohomology theory and vanishing theorems
- Riemann-Roch theorem
- Advanced topics in algebraic geometry

## References and Acknowledgments

- Ulrich Görtz and Torsten Wedhorn, *"Algebraic Geometry I"*, 2nd Edition, Springer (2020)
- [Mathlib Community](https://leanprover-community.github.io/) for the extensive mathematics library
- [Lean 4 Manual](https://lean-lang.org/lean4/doc/) for language documentation
- [Pietro Monticone's LeanProject template](https://github.com/pitmonticone/LeanProject) for the project structure and blueprint configuration

---

**Note**: This is an active formalization project. The code compiles with Lean 4.24.0 and Mathlib 4.24.0.
