# Formalizing Görtz-Wedhorn's Algebraic Geometry in Lean 4

[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-lightblue.svg)](https://opensource.org/licenses/Apache-2.0)
[![Lean 4](https://img.shields.io/badge/Lean-4.21.0-blue.svg)](https://leanprover-community.github.io/)
[![Mathlib](https://img.shields.io/badge/Mathlib-4.21.0-blue.svg)](https://github.com/leanprover-community/mathlib4)

A formalization project in **Lean 4** of selected results from Ulrich Görtz and Torsten Wedhorn's *"Algebraic Geometry I"* (2nd Edition). This repository serves as a portfolio demonstration of formal mathematics and proof verification capabilities in modern algebraic geometry.

## 🎯 Project Overview

This is a **learning project** to develop expertise in formalizing advanced algebraic geometry using Lean 4. The ultimate goal is to work toward significant theorems like **Bézout's theorem**, **Zariski's Main Theorem**, or other major results in algebraic geometry.

Currently, I'm building foundational infrastructure by formalizing basic results from Görtz-Wedhorn's textbook, starting with **Chapter 5: Schemes** and dimension theory. While these preliminary results (like Lemma 5.7) require substantial code due to the complexity of formalization, they're stepping stones toward the real mathematical milestones.

### 📚 Reference & Methodology

- **Primary Source**: Ulrich Görtz and Torsten Wedhorn, *"Algebraic Geometry I"*, 2nd Edition
- **Current Phase**: Foundational results on topological Krull dimension and scheme theory
- **Long-term Goals**: Major theorems like Bézout's theorem, Zariski's Main Theorem, or cohomological results
- **Purpose**: Personal learning project to master Lean 4 formalization techniques in algebraic geometry

### ✨ Current Progress

**Foundation Building (Chapter 5):**
- **Lemma 5.7**: Complete formalization of topological Krull dimension properties
- **Subspace dimension inequality**: `dim(Y) ≤ dim(X)` for subspaces
- **Proper closed subset dimension**: Strict inequality for proper closed subsets
- **Open cover dimension formula**: `dim(X) = sup{dim(U_i) : U_i open cover}`
- **Irreducible components dimension**: `dim(X) = sup{dim(Y) : Y irreducible component}`
- **Scheme dimension characterization**: Connection between topological and ring-theoretic dimensions

**Learning Outcomes So Far:**
- **~1350 lines** of Lean 4 code (substantial due to formalization complexity, not mathematical depth)
- **Infrastructure development**: Building the foundation needed for serious algebraic geometry
- **Technique mastery**: Advanced proof techniques in topological spaces, order theory, and categorical constructions
- **Understanding the gap**: Appreciating the difference between mathematical intuition and formal verification

## 🔧 Setup and Installation

### Prerequisites
- [Lean 4](https://leanprover-community.github.io/get_started.html) (version 4.21.0)
- [Lake](https://github.com/leanprover/lake) build system
- Git

### Quick Start
```bash
git clone https://github.com/ADA-Projects/Lean-AG.git
cd Lean-AG
lake exe cache get
lake build
```

## 📁 Repository Structure

```
Lean-AG/
├── GWchap5/                    # Main formalization directory
│   ├── gw_sect5-3.lean         # Core theorems and proofs (~1350 lines)
│   └── Mathlib/                # Additional Mathlib extensions
├── GWchap5.lean               # Root module imports
├── lakefile.toml              # Lake build configuration
├── lean-toolchain            # Lean version specification
└── README.md                  # This file
```

### 📋 File Descriptions

- **[`GWchap5/gw_sect5-3.lean`](GWchap5/gw_sect5-3.lean)**: Contains the main formalization work including:
  - Helper lemmas for closure operations in subspaces
  - Irreducible closed sets and their properties
  - Topological Krull dimension theory
  - Complete proof of Lemma 5.7 and related results
  - Scheme dimension characterizations

- **[`lakefile.toml`](lakefile.toml)**: Lake build system configuration with Mathlib dependencies
- **[`lean-toolchain`](lean-toolchain)**: Specifies Lean 4.21.0 for reproducible builds

## 🏗️ Formalized Theorems

### Current Foundation: Lemma 5.7 (Görtz-Wedhorn)

This **foundational lemma** establishes basic properties of topological Krull dimension. While not a deep result in algebraic geometry, its formalization demonstrates the infrastructure needed for serious theorems:

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

**Topological Foundations:**
- `closure_in_subspace_eq_inter`: Characterization of closures in subspace topology
- `map_irreducible_closed_injective`: Injectivity of maps between irreducible closed sets
- `map_irreducible_closed_strictMono`: Strict monotonicity properties

**Dimension Theory:**
- `top_KrullDim_subspace_le`: Dimension inequality for subspaces
- `topological_dim_proper_closed_subset_lt`: Strict inequality for proper subsets
- `topological_dim_open_cover`: Dimension via open covers
- `topological_dim_irreducible_components`: Dimension via irreducible components
- `scheme_dim_eq_sup_local_rings`: Scheme dimension via local ring dimensions


## 🚀 Learning Roadmap

This project is building toward major algebraic geometry theorems through systematic foundation building:

### Near-term (Building Infrastructure)
1. **Complete Chapter 5**: Finish basic scheme theory and morphism properties
2. **Geometric Constructions**: Projective spaces, blow-ups, and basic varieties
3. **Intersection Theory Foundations**: Cycles, divisors, and intersection products

### Medium-term (Substantial Results)
4. **Bézout's Theorem**: Intersection multiplicities and degree bounds
5. **Zariski's Main Theorem**: Proper morphisms and normalizations
6. **Cohomology Theory**: Sheaf cohomology and vanishing theorems

### Long-term (Deep Theorems)
7. **Riemann-Roch**: For curves and surfaces
8. **Resolution of Singularities**: In characteristic zero
9. **Advanced Topics**: Étale cohomology, scheme theory applications

*Note: This is an ambitious learning timeline - each step involves substantial technical development.*

## 🤝 Contributing & Collaboration

While this is primarily a portfolio project, I welcome:
- **Code Reviews**: Feedback on proof techniques and organization
- **Mathematical Discussion**: Insights on alternative approaches or generalizations
- **Educational Use**: Feel free to use this as a learning resource for Lean 4

## 📚 References & Acknowledgments

- Ulrich Görtz and Torsten Wedhorn, *"Algebraic Geometry I"*, 2nd Edition, Springer (2020)
- [Mathlib Community](https://leanprover-community.github.io/) for the extensive mathematics library
- [Lean 4 Manual](https://lean-lang.org/lean4/doc/) for language documentation
- [Pietro Monticone's LeanProject template](https://github.com/pitmonticone/LeanProject) for the project structure and blueprint configuration

---

**Note**: This is an **active learning project** in mathematical formalization. The current results are foundational - the real mathematical goals lie ahead. The code compiles with Lean 4.21.0 and Mathlib 4.21.0.
