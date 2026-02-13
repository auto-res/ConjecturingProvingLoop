import Mathlib
import Aesop

namespace Topology

variable {X : Type*} [TopologicalSpace X]

def P1 (A : Set X) : Prop :=
  A ⊆ closure (interior A)

def P2 (A : Set X) : Prop :=
  A ⊆ interior (closure (interior A))

def P3 (A : Set X) : Prop :=
  A ⊆ interior (closure A)


theorem P2_to_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P1 A := by
  intro hA
  exact hA.trans interior_subset

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P1 A → P1 B → P1 (A ∪ B) := by
  intro hA hB
  intro x hx
  cases hx with
  | inl hAx =>
      have hxA : x ∈ closure (interior A) := hA hAx
      have hsubset : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono (interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B))
      exact hsubset hxA
  | inr hBx =>
      have hxB : x ∈ closure (interior B) := hB hBx
      have hsubset : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono (interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B))
      exact hsubset hxB

theorem P2_empty {X : Type*} [TopologicalSpace X] : P2 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P3_univ {X : Type*} [TopologicalSpace X] : P3 (Set.univ : Set X) := by
  intro x hx
  simpa [closure_univ, interior_univ] using hx

theorem P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → P3 A := by
  intro hAopen
  intro x hx
  have hx_int : x ∈ interior A := by
    simpa [hAopen.interior_eq] using hx
  have h_subset : interior A ⊆ interior (closure A) :=
    interior_mono subset_closure
  exact h_subset hx_int

theorem interior_subset_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → interior A ⊆ interior (closure (interior A)) := by
  intro hP2
  exact interior_subset.trans hP2

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P2 A → P2 B → P2 (A ∪ B) := by
  intro hA hB
  intro x hx
  cases hx with
  | inl hAx =>
      have hxA : x ∈ interior (closure (interior A)) := hA hAx
      have hsubset : interior (closure (interior A)) ⊆
          interior (closure (interior (A ∪ B))) := by
        have h₁ : interior A ⊆ interior (A ∪ B) :=
          interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
        have h₂ : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
          closure_mono h₁
        exact interior_mono h₂
      exact hsubset hxA
  | inr hBx =>
      have hxB : x ∈ interior (closure (interior B)) := hB hBx
      have hsubset : interior (closure (interior B)) ⊆
          interior (closure (interior (A ∪ B))) := by
        have h₁ : interior B ⊆ interior (A ∪ B) :=
          interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
        have h₂ : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
          closure_mono h₁
        exact interior_mono h₂
      exact hsubset hxB

theorem P1_empty {X : Type*} [TopologicalSpace X] : P1 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P2_univ {X : Type*} [TopologicalSpace X] : P2 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P3_empty {X : Type*} [TopologicalSpace X] : P3 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → P2 A := by
  intro hAopen x hx
  simpa [hAopen.interior_eq] using (P3_of_open hAopen) hx

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} : (∀ A ∈ 𝒜, P3 A) → P3 (⋃₀ 𝒜) := by
  intro hP3
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP3A : P3 A := hP3 A hA_mem
  have hx_int_clA : x ∈ interior (closure A) := hP3A hxA
  have hsubset : interior (closure A) ⊆ interior (closure (⋃₀ 𝒜)) := by
    apply interior_mono
    apply closure_mono
    exact Set.subset_sUnion_of_mem hA_mem
  exact hsubset hx_int_clA

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P3 A → P3 B → P3 (A ∪ B) := by
  intro hA hB
  intro x hx
  cases hx with
  | inl hAx =>
      have hx_int_clA : x ∈ interior (closure A) := hA hAx
      have hsubset : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        apply closure_mono
        exact Set.subset_union_left
      exact hsubset hx_int_clA
  | inr hBx =>
      have hx_int_clB : x ∈ interior (closure B) := hB hBx
      have hsubset : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        apply closure_mono
        exact Set.subset_union_right
      exact hsubset hx_int_clB

theorem P1_univ {X : Type*} [TopologicalSpace X] : P1 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} : (∀ A ∈ 𝒜, P2 A) → P2 (⋃₀ 𝒜) := by
  intro hP2
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP2A : P2 A := hP2 A hA_mem
  have hx_in : x ∈ interior (closure (interior A)) := hP2A hxA
  have h_subset :
      interior (closure (interior A)) ⊆
        interior (closure (interior (⋃₀ 𝒜))) := by
    -- First, relate `interior A` to `interior (⋃₀ 𝒜)`.
    have h1 : interior A ⊆ interior (⋃₀ 𝒜) :=
      interior_mono (Set.subset_sUnion_of_mem hA_mem)
    -- Then, take closures of both sides.
    have h2 : closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) :=
      closure_mono h1
    -- Finally, take interiors again.
    exact interior_mono h2
  exact h_subset hx_in

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} : (∀ A ∈ 𝒜, P1 A) → P1 (⋃₀ 𝒜) := by
  intro hP1
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP1A : P1 A := hP1 A hA_mem
  have hx_closure : x ∈ closure (interior A) := hP1A hxA
  have h_subset : closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) := by
    apply closure_mono
    apply interior_mono
    exact Set.subset_sUnion_of_mem hA_mem
  exact h_subset hx_closure

theorem P2_to_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P3 A := by
  intro hP2
  intro x hx
  have hx_int : x ∈ interior (closure (interior A)) := hP2 hx
  have h_subset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have h_closure : closure (interior A) ⊆ closure A :=
      closure_mono interior_subset
    exact interior_mono h_closure
  exact h_subset hx_int

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} : closure A = Set.univ → P3 A := by
  intro hDense x hx
  simpa [hDense, interior_univ] using (Set.mem_univ x)

theorem P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → P1 (closure A) := by
  intro hP1
  intro x hx
  -- Step 1: bring `x` from `closure A` into `closure (interior A)`.
  have hx₁ : x ∈ closure (interior A) := by
    have hsubset : (closure A : Set X) ⊆ closure (interior A) := by
      simpa [closure_closure] using (closure_mono hP1)
    exact hsubset hx
  -- Step 2: use monotonicity to land in the desired set.
  have hsubset₂ : closure (interior A) ⊆ closure (interior (closure A)) := by
    have h' : (interior A : Set X) ⊆ interior (closure A) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    exact closure_mono h'
  exact hsubset₂ hx₁

theorem P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : interior A = Set.univ) : P3 A := by
  intro x _
  have hx_int : x ∈ interior A := by
    simpa [h] using Set.mem_univ x
  exact (interior_mono subset_closure) hx_int

theorem P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (interior A) := by
  intro x hx
  have hx' : x ∈ interior (interior A) := by
    simpa [interior_interior] using hx
  exact subset_closure hx'

theorem P1_of_open {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → P1 A := by
  intro hAopen
  intro x hx
  have hx_int : x ∈ interior A := by
    simpa [hAopen.interior_eq] using hx
  exact subset_closure hx_int

theorem P2_iff_P3_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P2 A ↔ P3 A := by
  -- `P2 A → P3 A` holds without any extra assumptions
  have h₁ : P2 A → P3 A := fun h => P2_to_P3 h
  -- Prove `P3 A → P2 A` assuming `A` is closed
  have h₂ : P3 A → P2 A := by
    intro hP3
    intro x hxA
    -- From `hP3` we obtain that `x ∈ interior A`
    have hx_intA : x ∈ interior A := by
      have hx : x ∈ interior (closure A) := hP3 hxA
      simpa [hA.closure_eq] using hx
    -- Show that `interior A ⊆ interior (closure (interior A))`
    have h_subset : interior A ⊆ interior (closure (interior A)) := by
      have h' : interior (interior A) ⊆ interior (closure (interior A)) :=
        interior_mono (subset_closure : (interior A : Set X) ⊆ closure (interior A))
      simpa [interior_interior] using h'
    exact h_subset hx_intA
  exact ⟨h₁, h₂⟩

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} : interior A = Set.univ → P2 A := by
  intro hIntUniv
  intro x _
  simpa [hIntUniv, closure_univ, interior_univ] using (Set.mem_univ x)

theorem closure_interior_eq_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → closure (interior A) = closure A := by
  intro hP1
  apply Set.Subset.antisymm
  · exact closure_mono interior_subset
  ·
    have hsubset : (A : Set X) ⊆ closure (interior A) := hP1
    have hclosure : closure A ⊆ closure (closure (interior A)) := closure_mono hsubset
    simpa [closure_closure] using hclosure

theorem P1_iff_P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P1 A ↔ P2 A := by
  refine ⟨?fwd, ?rev⟩
  · intro _hP1
    intro x hx
    have hx_int : x ∈ interior (closure A) :=
      (interior_maximal subset_closure hA) hx
    simpa [hA.interior_eq] using hx_int
  · intro hP2
    exact P2_to_P1 (A := A) hP2

theorem interior_closure_eq_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → interior (closure A) = interior (closure (interior A)) := by
  intro hP2
  -- `P2 A` implies `P1 A`
  have hP1 : P1 A := P2_to_P1 (A := A) hP2
  -- hence the two closures coincide
  have hClosureEq : closure (interior A : Set X) = closure A :=
    closure_interior_eq_of_P1 (A := A) hP1
  -- rewriting with this equality finishes the proof
  simpa [hClosureEq]

theorem P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} : interior A = Set.univ → P1 A := by
  intro hIntUniv
  exact P2_to_P1 (A := A) ((P2_of_dense_interior (A := A)) hIntUniv)

theorem P1_closed_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → P3 A → P1 A := by
  intro hClosed hP3
  have hP2 : P2 A := (P2_iff_P3_of_closed (X := X) (A := A) hClosed).2 hP3
  exact P2_to_P1 (A := A) hP2

theorem P2_unionᵢ {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} : (∀ i, P2 (A i)) → P2 (⋃ i, A i) := by
  intro hP2
  intro x hx
  -- Obtain an index `i` such that `x ∈ A i`.
  rcases Set.mem_iUnion.1 hx with ⟨i, hxAi⟩
  -- Apply `P2` for `A i`.
  have hP2i : P2 (A i) := hP2 i
  have hx_in : x ∈ interior (closure (interior (A i))) := hP2i hxAi
  -- Relate the relevant interiors/closures to those of the big union.
  have hsubset :
      interior (closure (interior (A i))) ⊆
        interior (closure (interior (⋃ j, A j))) := by
    -- `interior (A i)` is contained in `interior (⋃ j, A j)`.
    have h1 : interior (A i) ⊆ interior (⋃ j, A j) := by
      have hAisub : (A i : Set X) ⊆ ⋃ j, A j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono hAisub
    -- Take closures, then interiors again.
    have h2 : closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) :=
      closure_mono h1
    exact interior_mono h2
  exact hsubset hx_in

theorem P3_unionᵢ {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} : (∀ i, P3 (A i)) → P3 (⋃ i, A i) := by
  intro hP3
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxAi⟩
  have hP3i : P3 (A i) := hP3 i
  have hx_int : x ∈ interior (closure (A i)) := hP3i hxAi
  have hsubset : interior (closure (A i)) ⊆ interior (closure (⋃ j, A j)) := by
    have hAi_sub : (A i : Set X) ⊆ ⋃ j, A j := by
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    have h_closure : closure (A i) ⊆ closure (⋃ j, A j) :=
      closure_mono hAi_sub
    exact interior_mono h_closure
  exact hsubset hx_int

theorem P1_iff_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ closure (interior A) = closure A := by
  constructor
  · intro hP1
    exact closure_interior_eq_of_P1 (A := A) hP1
  · intro hEq
    intro x hx
    have hx_cl : x ∈ closure A := subset_closure hx
    simpa [hEq] using hx_cl

theorem P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P2 (interior A) := by
  intro x hx
  have hsubset : (interior A : Set X) ⊆ interior (closure (interior A)) :=
    interior_maximal subset_closure isOpen_interior
  have : x ∈ interior (closure (interior A)) := hsubset hx
  simpa [interior_interior] using this

theorem closure_interior_eq_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → closure (interior A) = closure A := by
  intro hP2
  exact closure_interior_eq_of_P1 (A := A) (P2_to_P1 (A := A) hP2)

theorem P2_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P2 A → P2 B → P2 (Set.prod A B) := by
  intro hP2A hP2B
  intro p hpProd
  rcases hpProd with ⟨hpA, hpB⟩
  -- Auxiliary open sets in the two coordinates.
  set SA := interior (closure (interior A)) with hSAdef
  set SB := interior (closure (interior B)) with hSBdef
  have hSA : p.1 ∈ SA := by
    have : p.1 ∈ interior (closure (interior A)) := hP2A hpA
    simpa [hSAdef] using this
  have hSB : p.2 ∈ SB := by
    have : p.2 ∈ interior (closure (interior B)) := hP2B hpB
    simpa [hSBdef] using this
  -- An open neighbourhood of `p` in the product space.
  let O : Set (X × Y) := Set.prod SA SB
  have hOopen : IsOpen O := by
    have hSAopen : IsOpen SA := by
      have : IsOpen (interior (closure (interior A))) := isOpen_interior
      simpa [hSAdef] using this
    have hSBopen : IsOpen SB := by
      have : IsOpen (interior (closure (interior B))) := isOpen_interior
      simpa [hSBdef] using this
    simpa [O] using hSAopen.prod hSBopen
  have hpO : p ∈ O := by
    dsimp [O]; exact ⟨hSA, hSB⟩
  -- Show that this neighbourhood is contained in the desired set.
  have hO_sub : O ⊆ closure (interior (Set.prod A B)) := by
    intro q hqO
    dsimp [O] at hqO
    rcases hqO with ⟨hqSA, hqSB⟩
    have hqClA : q.1 ∈ closure (interior A) := interior_subset hqSA
    have hqClB : q.2 ∈ closure (interior B) := interior_subset hqSB
    have hqProdCl :
        q ∈ Set.prod (closure (interior A)) (closure (interior B)) :=
      ⟨hqClA, hqClB⟩
    -- `closure (interior A × interior B)` equals this product.
    have h_cl_eq :
        closure (Set.prod (interior A) (interior B)) =
          Set.prod (closure (interior A)) (closure (interior B)) := by
      simpa using closure_prod_eq (s := interior A) (t := interior B)
    have hq_in_closure_prod :
        q ∈ closure (Set.prod (interior A) (interior B)) := by
      simpa [h_cl_eq] using hqProdCl
    -- Relate the two closures via monotonicity.
    have h_subset :
        closure (Set.prod (interior A) (interior B)) ⊆
          closure (interior (Set.prod A B)) := by
      -- First, `interior A × interior B` lies in `interior (A × B)`.
      have h_sub :
          Set.prod (interior A) (interior B) ⊆ interior (Set.prod A B) := by
        have h_open : IsOpen (Set.prod (interior A) (interior B)) :=
          (isOpen_interior.prod isOpen_interior)
        have h_sub' :
            Set.prod (interior A) (interior B) ⊆ Set.prod A B := by
          intro r hr
          rcases hr with ⟨hrA, hrB⟩
          exact ⟨interior_subset hrA, interior_subset hrB⟩
        exact interior_maximal h_sub' h_open
      exact closure_mono h_sub
    exact h_subset hq_in_closure_prod
  -- Use `O` to witness that `p` is in the required interior.
  have h_nhds : O ∈ 𝓝 p := hOopen.mem_nhds hpO
  have h_mem :
      p ∈ interior (closure (interior (Set.prod A B))) :=
    (mem_interior_iff_mem_nhds).2 (Filter.mem_of_superset h_nhds hO_sub)
  simpa [O, hSAdef, hSBdef] using h_mem

theorem P1_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P1 A → P1 B → P1 (Set.prod A B) := by
  intro hP1A hP1B
  intro p hpProd
  rcases hpProd with ⟨hpA, hpB⟩
  -- Coordinates lie in the respective closures of the interiors
  have hx_cl : p.1 ∈ closure (interior A) := hP1A hpA
  have hy_cl : p.2 ∈ closure (interior B) := hP1B hpB
  -- Hence the point lies in the product of these closures
  have hp_prod_cl : p ∈ Set.prod (closure (interior A)) (closure (interior B)) :=
    ⟨hx_cl, hy_cl⟩
  -- Identify this product with the closure of the product of the interiors
  have h_cl_eq :
      closure (Set.prod (interior A) (interior B)) =
        Set.prod (closure (interior A)) (closure (interior B)) := by
    simpa using closure_prod_eq (s := interior A) (t := interior B)
  have hp_in_cl : p ∈ closure (Set.prod (interior A) (interior B)) := by
    simpa [h_cl_eq] using hp_prod_cl
  -- The closure we have is contained in the desired closure
  have h_subset :
      closure (Set.prod (interior A) (interior B)) ⊆
        closure (interior (Set.prod A B)) := by
    -- First show the underlying sets are related
    have h_sub :
        Set.prod (interior A) (interior B) ⊆ interior (Set.prod A B) := by
      have h_open : IsOpen (Set.prod (interior A) (interior B)) :=
        (isOpen_interior.prod isOpen_interior)
      have h_sub' :
          Set.prod (interior A) (interior B) ⊆ Set.prod A B := by
        intro q hq
        rcases hq with ⟨hqa, hqb⟩
        exact ⟨interior_subset hqa, interior_subset hqb⟩
      exact interior_maximal h_sub' h_open
    exact closure_mono h_sub
  exact h_subset hp_in_cl

theorem P3_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P3 A → P3 B → P3 (Set.prod A B) := by
  intro hP3A hP3B
  intro p hpProd
  rcases hpProd with ⟨hpA, hpB⟩
  -- coordinates live in the relevant interiors of closures
  have hSA_mem : p.1 ∈ interior (closure A) := hP3A hpA
  have hSB_mem : p.2 ∈ interior (closure B) := hP3B hpB
  -- auxiliary open sets
  set SA := interior (closure A) with hSAdef
  set SB := interior (closure B) with hSBdef
  -- open neighbourhood around `p`
  let O : Set (X × Y) := Set.prod SA SB
  have hOopen : IsOpen O := by
    have hSAopen : IsOpen SA := by
      have : IsOpen (interior (closure A)) := isOpen_interior
      simpa [hSAdef] using this
    have hSBopen : IsOpen SB := by
      have : IsOpen (interior (closure B)) := isOpen_interior
      simpa [hSBdef] using this
    simpa [O] using hSAopen.prod hSBopen
  have hpO : p ∈ O := by
    dsimp [O]
    have hpSA : p.1 ∈ SA := by
      simpa [hSAdef] using hSA_mem
    have hpSB : p.2 ∈ SB := by
      simpa [hSBdef] using hSB_mem
    exact ⟨hpSA, hpSB⟩
  -- `O` is contained in the interior of the desired closure
  have hO_sub : O ⊆ interior (closure (Set.prod A B)) := by
    -- first show `O ⊆ closure (A × B)`
    have hO_sub_cl : O ⊆ closure (Set.prod A B) := by
      intro q hqO
      dsimp [O] at hqO
      rcases hqO with ⟨hqSA, hqSB⟩
      -- coordinates lie in the respective closures
      have hq_clA : q.1 ∈ closure A := by
        have : q.1 ∈ interior (closure A) := by
          simpa [hSAdef] using hqSA
        exact interior_subset this
      have hq_clB : q.2 ∈ closure B := by
        have : q.2 ∈ interior (closure B) := by
          simpa [hSBdef] using hqSB
        exact interior_subset this
      have hq_prod : q ∈ Set.prod (closure A) (closure B) := ⟨hq_clA, hq_clB⟩
      have h_closure_prod_eq : closure (Set.prod A B) = Set.prod (closure A) (closure B) := by
        simpa using closure_prod_eq (s := A) (t := B)
      simpa [h_closure_prod_eq] using hq_prod
    -- use `interior_maximal`
    exact interior_maximal hO_sub_cl hOopen
  -- conclude the desired membership
  have hp_int : p ∈ interior (closure (Set.prod A B)) := hO_sub hpO
  simpa using hp_int

theorem P1_prod_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : P1 A → P1 (Set.prod A (Set.univ : Set Y)) := by
  intro hP1A
  simpa using
    (P1_prod (A := A) (B := (Set.univ : Set Y)) hP1A (P1_univ (X := Y)))

theorem P2_prod_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} : P2 B → P2 (Set.prod (Set.univ : Set X) B) := by
  intro hP2B
  simpa using
    (P2_prod (A := (Set.univ : Set X)) (B := B) (P2_univ (X := X)) hP2B)

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P3 A → P3 (interior A) := by
  intro _
  exact P3_of_open (A := interior A) isOpen_interior

theorem P2_prod_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : P2 A → P2 (Set.prod A (Set.univ : Set Y)) := by
  intro hP2A
  simpa using
    (P2_prod (A := A) (B := (Set.univ : Set Y)) hP2A (P2_univ (X := Y)))

theorem P3_prod_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} : P3 B → P3 (Set.prod (Set.univ : Set X) B) := by
  intro hP3B
  simpa using
    (P3_prod (A := (Set.univ : Set X)) (B := B) (P3_univ (X := X)) hP3B)

theorem P1_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : P1 A → P1 B → P1 C → P1 (Set.prod (Set.prod A B) C) := by
  intro hP1A hP1B hP1C
  -- First build the property for `A × B`
  have hP1AB : P1 (Set.prod A B) :=
    P1_prod (A := A) (B := B) hP1A hP1B
  -- Then apply the binary product lemma once more with `C`
  exact
    P1_prod (X := X × Y) (Y := Z) (A := Set.prod A B) (B := C) hP1AB hP1C

theorem P2_iff_P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} : interior A = Set.univ → (P2 A ↔ P1 A) := by
  intro hInt
  refine ⟨?forward, ?backward⟩
  · intro hP2
    exact P2_to_P1 (A := A) hP2
  · intro _hP1
    exact (P2_of_dense_interior (A := A)) hInt

theorem P3_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : P3 A → P3 B → P3 C → P3 (Set.prod (Set.prod A B) C) := by
  intro hP3A hP3B hP3C
  -- Build the property for `A × B`
  have hP3AB : P3 (Set.prod A B) :=
    P3_prod (A := A) (B := B) hP3A hP3B
  -- Combine with `C`
  exact
    P3_prod (X := X × Y) (Y := Z) (A := Set.prod A B) (B := C) hP3AB hP3C

theorem P2_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : P2 A → P2 B → P2 C → P2 (Set.prod (Set.prod A B) C) := by
  intro hP2A hP2B hP2C
  -- First, establish `P2` for `A × B`.
  have hP2AB : P2 (Set.prod A B) :=
    P2_prod (A := A) (B := B) hP2A hP2B
  -- Then, combine with `C`.
  exact
    P2_prod (X := X × Y) (Y := Z) (A := Set.prod A B) (B := C) hP2AB hP2C

theorem P2_iff_P3_of_interior_dense {X : Type*} [TopologicalSpace X] {A : Set X} : closure (interior A) = Set.univ → (P2 A ↔ P3 A) := by
  intro hDense
  refine ⟨?forward, ?backward⟩
  · intro hP2
    exact P2_to_P3 (A := A) hP2
  · intro _hP3
    intro x hx
    simpa [hDense, interior_univ] using (Set.mem_univ x)

theorem P2_iff_P1_of_closed_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : IsClosed (interior A)) : P2 A ↔ P1 A := by
  refine ⟨?forward, ?backward⟩
  · intro hP2
    exact P2_to_P1 (A := A) hP2
  · intro hP1
    intro x hxA
    -- Since `interior A` is closed, its closure is itself.
    have h_cl : closure (interior A : Set X) = interior A := h.closure_eq
    -- From `P1`, we obtain `A ⊆ interior A`.
    have h_sub : (A : Set X) ⊆ interior A := by
      intro y hy
      have : y ∈ closure (interior A) := hP1 hy
      simpa [h_cl] using this
    have hx_int : x ∈ interior A := h_sub hxA
    -- Rewriting with `h_cl` finishes the goal.
    simpa [h_cl, interior_interior] using hx_int

theorem P2_sigma {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] {A : ∀ i, Set (X i)} : (∀ i, P2 (A i)) → P2 {p : Σ i, X i | P2 (A p.1)} := by
  intro hAll
  -- The set in question is actually the whole space.
  have h_eq :
      ({p : Sigma X | P2 (A p.1)} : Set (Sigma X)) = Set.univ := by
    ext p
    constructor
    · intro _
      exact Set.mem_univ _
    · intro _
      exact hAll p.1
  -- `P2` holds for `Set.univ`, hence for our set.
  simpa [h_eq.symm] using (P2_univ (X := Sigma X))

theorem P3_closed_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → P2 A → P3 A := by
  intro _ hP2
  exact P2_to_P3 (A := A) hP2

theorem P3_sigma {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] {A : ∀ i, Set (X i)} : (∀ i, P3 (A i)) → P3 {p : Σ i, X i | P3 (A p.1)} := by
  intro hAll
  -- The set in question is actually the whole space.
  have h_eq :
      ({p : Sigma X | P3 (A p.1)} : Set (Sigma X)) = Set.univ := by
    ext p
    constructor
    · intro _
      exact Set.mem_univ _
    · intro _
      exact hAll p.1
  -- `P3` holds for `Set.univ`, hence for our set.
  simpa [h_eq.symm] using (P3_univ (X := Sigma X))

theorem P1_sigma {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] {A : ∀ i, Set (X i)} : (∀ i, P1 (A i)) → P1 {p : Σ i, X i | P1 (A p.1)} := by
  intro hAll
  have h_eq :
      ({p : Sigma X | P1 (A p.1)} : Set (Sigma X)) = Set.univ := by
    ext p
    constructor
    · intro _
      exact Set.mem_univ _
    · intro _
      exact hAll p.1
  simpa [h_eq.symm] using (P1_univ (X := Sigma X))

theorem P2_prod_four {W X Y Z : Type*} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set W} {B : Set X} {C : Set Y} {D : Set Z} : P2 A → P2 B → P2 C → P2 D → P2 (Set.prod (Set.prod (Set.prod A B) C) D) := by
  intro hP2A hP2B hP2C hP2D
  -- First, combine `A` and `B`.
  have hP2AB : P2 (Set.prod A B) :=
    P2_prod (A := A) (B := B) hP2A hP2B
  -- Next, combine the result with `C`.
  have hP2ABC : P2 (Set.prod (Set.prod A B) C) :=
    P2_prod (A := Set.prod A B) (B := C) hP2AB hP2C
  -- Finally, combine with `D`.
  exact
    P2_prod (A := Set.prod (Set.prod A B) C) (B := D) hP2ABC hP2D

theorem P3_iff_P1_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P3 A ↔ P1 A := by
  refine ⟨?forward, ?backward⟩
  · intro hP3
    intro x hxA
    -- From `P3` we get `x ∈ interior (closure A)`.
    have hx_int : x ∈ interior (closure A) := hP3 hxA
    -- Hence `x ∈ closure A`.
    have hx_cl : x ∈ closure A := interior_subset hx_int
    -- Since `A` is open, `interior A = A`, so
    -- `closure (interior A) = closure A`.
    simpa [hA.interior_eq] using hx_cl
  · intro _hP1
    intro x hxA
    -- Because `A` is open and contained in its closure,
    -- every point of `A` lies in `interior (closure A)`.
    have h_sub : (A : Set X) ⊆ interior (closure A) :=
      interior_maximal subset_closure hA
    exact h_sub hxA

theorem P2_of_P3_and_closed {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → P3 A → P2 A := by
  intro hClosed hP3
  intro x hxA
  -- From `P3` we know `x ∈ interior (closure A)`, but `closure A = A` since `A` is closed.
  have hx_intA : x ∈ interior A := by
    have : x ∈ interior (closure A) := hP3 hxA
    simpa [hClosed.closure_eq] using this
  -- Now, `interior A` is contained in `interior (closure (interior A))`.
  have h_subset : interior A ⊆ interior (closure (interior A)) := by
    have h' : interior (interior A) ⊆ interior (closure (interior A)) :=
      interior_mono (subset_closure : (interior A : Set X) ⊆ closure (interior A))
    simpa [interior_interior] using h'
  exact h_subset hx_intA

theorem P1_unionᵢ {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} : (∀ i, P1 (A i)) → P1 (⋃ i, A i) := by
  intro hP1
  intro x hxUnion
  rcases Set.mem_iUnion.1 hxUnion with ⟨i, hxAi⟩
  -- Use the hypothesis for the chosen index.
  have hP1i : P1 (A i) := hP1 i
  have hx_cl : x ∈ closure (interior (A i)) := hP1i hxAi
  -- Relate the closures/interiors of the individual set and the big union.
  have h_subset : closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) := by
    -- First, relate the interiors.
    have h_int : interior (A i) ⊆ interior (⋃ j, A j) := by
      have hAi_sub : (A i : Set X) ⊆ ⋃ j, A j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono hAi_sub
    -- Then take closures.
    exact closure_mono h_int
  exact h_subset hx_cl

theorem P3_of_dense_subset {X : Type*} [TopologicalSpace X] {A B : Set X} : A ⊆ B → closure A = Set.univ → P3 B := by
  intro hAB hDense
  -- First, show that `closure B = univ`.
  have hDenseB : closure (B : Set X) = Set.univ := by
    apply Set.Subset.antisymm
    · exact Set.subset_univ _
    · intro x _
      -- Since `closure A = univ`, every point is in `closure A`,
      -- and hence (by monotonicity) in `closure B`.
      have hxA : x ∈ closure (A : Set X) := by
        simpa [hDense] using (Set.mem_univ x)
      exact (closure_mono hAB) hxA
  -- Now apply the previously proved lemma.
  exact P3_of_dense (A := B) hDenseB

theorem P3_iff_P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P3 A ↔ P2 A := by
  simpa using
    ((P3_iff_P1_of_open (A := A) hA).trans (P1_iff_P2_of_open (A := A) hA))

theorem P1_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ Y) {A : Set X} : P1 A → P1 (f '' A) := by
  intro hP1
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` comes from `A`
  have hx_cl : x ∈ closure (interior A) := hP1 hxA
  -- Use the neighborhood characterization of the closure
  refine (mem_closure_iff).2 ?_
  intro V hVopen hfxV
  -- Pull the neighbourhood `V` back through `f`
  have hUopen : IsOpen (f ⁻¹' V) := hVopen.preimage f.continuous
  have hxU : x ∈ f ⁻¹' V := by
    simpa [Set.mem_preimage] using hfxV
  -- Since `x` is in the closure of `interior A`, the pull-back meets `interior A`
  have h_nonempty : ((f ⁻¹' V) ∩ interior A).Nonempty := by
    have := (mem_closure_iff).1 hx_cl (f ⁻¹' V) hUopen hxU
    simpa using this
  rcases h_nonempty with ⟨z, hzU, hzIntA⟩
  have hzV : f z ∈ V := by
    simpa [Set.mem_preimage] using hzU
  -- Show that `f z` lies in `interior (f '' A)`
  have hzIntFA : f z ∈ interior (f '' A) := by
    -- `f '' interior A` is an open subset of `f '' A`
    have h_open_fint : IsOpen (f '' interior A) := by
      have hf : IsOpenMap f := f.isOpenMap
      simpa using hf (interior A) isOpen_interior
    have h_sub_fint : (f '' interior A : Set _) ⊆ f '' A := by
      intro w hw
      rcases hw with ⟨u, huInt, rfl⟩
      exact ⟨u, interior_subset huInt, rfl⟩
    have h_subset : (f '' interior A : Set _) ⊆ interior (f '' A) :=
      interior_maximal h_sub_fint h_open_fint
    have hfz_mem : f z ∈ f '' interior A := ⟨z, hzIntA, rfl⟩
    exact h_subset hfz_mem
  exact ⟨f z, ⟨hzV, hzIntFA⟩⟩

theorem P2_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ Y) {B : Set Y} : P2 B → P2 (f ⁻¹' B) := by
  intro hP2B
  intro x hx
  -- `hx` gives `f x ∈ B`.
  have hfxB : f x ∈ B := by
    simpa [Set.mem_preimage] using hx
  -- Apply `P2 B`.
  have hfx : f x ∈ interior (closure (interior B)) := hP2B hfxB
  -- Auxiliary open sets in `Y` and their preimages in `X`.
  set V : Set Y := interior (closure (interior B)) with hVdef
  have hVopen : IsOpen V := by
    simpa [hVdef] using isOpen_interior
  have hfxV : f x ∈ V := by
    simpa [hVdef] using hfx
  set U : Set X := f ⁻¹' V with hUdef
  have hUopen : IsOpen U := by
    have : IsOpen (f ⁻¹' V) := hVopen.preimage f.continuous
    simpa [hUdef] using this
  have hxU : x ∈ U := by
    simpa [hUdef, Set.mem_preimage] using hfxV
  -- Show that every point of `U` lies in `closure (interior (f ⁻¹' B))`.
  have hU_sub : (U : Set X) ⊆ closure (interior (f ⁻¹' B)) := by
    intro y hyU
    -- `f y` lies in `V`.
    have hfyV : f y ∈ V := by
      simpa [hUdef, Set.mem_preimage] using hyU
    -- Hence `f y ∈ closure (interior B)`.
    have hfy_cl : f y ∈ closure (interior B) := by
      have hVsubset : (V : Set Y) ⊆ closure (interior B) := by
        intro z hz
        exact interior_subset hz
      exact hVsubset hfyV
    -- Prove `y ∈ closure (interior (f ⁻¹' B))`.
    have : y ∈ closure (interior (f ⁻¹' B)) := by
      -- Neighbourhood characterization of the closure.
      apply (mem_closure_iff).2
      intro W hWopen hyW
      -- Open set in `Y` obtained via `f.symm`.
      set T : Set Y := f.symm ⁻¹' W with hTdef
      have hTopen : IsOpen T := by
        have : IsOpen (f.symm ⁻¹' W) := hWopen.preimage f.symm.continuous
        simpa [hTdef] using this
      -- `f y` belongs to `T`.
      have hfyT : f y ∈ T := by
        have : y ∈ W := hyW
        simpa [hTdef, Set.mem_preimage, f.symm_apply_apply] using this
      -- Intersect with `interior B`.
      have hNonempty : (T ∩ interior B).Nonempty :=
        (mem_closure_iff).1 hfy_cl T hTopen hfyT
      rcases hNonempty with ⟨z, hzT, hzInt⟩
      -- Pull the point back to `X`.
      have hwW : f.symm z ∈ W := by
        have : z ∈ T := hzT
        simpa [hTdef, Set.mem_preimage] using this
      have hwInt : f.symm z ∈ interior (f ⁻¹' B) := by
        -- First, membership in `f ⁻¹' interior B`.
        have hw_pre : f.symm z ∈ f ⁻¹' interior B := by
          have : f (f.symm z) ∈ interior B := by
            simpa [f.apply_symm_apply] using hzInt
          simpa [Set.mem_preimage] using this
        -- Upgrade to the interior using maximality.
        have hOpenPre : IsOpen (f ⁻¹' interior B) :=
          (isOpen_interior).preimage f.continuous
        have hSub : (f ⁻¹' interior B : Set X) ⊆ f ⁻¹' B := by
          intro t ht
          simpa [Set.mem_preimage] using interior_subset ht
        have hSubset :
            (f ⁻¹' interior B : Set X) ⊆ interior (f ⁻¹' B) :=
          interior_maximal hSub hOpenPre
        exact hSubset hw_pre
      exact ⟨f.symm z, ⟨hwW, hwInt⟩⟩
    simpa using this
  -- Use the open neighbourhood `U` to finish.
  have hNhd : (U : Set X) ∈ 𝓝 x := hUopen.mem_nhds hxU
  have h_mem : x ∈ interior (closure (interior (f ⁻¹' B))) :=
    (mem_interior_iff_mem_nhds).2 (Filter.mem_of_superset hNhd hU_sub)
  simpa using h_mem

theorem interior_subset_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : P3 A → interior A ⊆ interior (closure A) := by
  intro _hP3
  exact interior_mono (subset_closure : (A : Set X) ⊆ closure A)

theorem P2_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ Y) {A : Set X} : P2 A → P2 (f '' A) := by
  intro hP2
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x ∈ A`, obtain the auxiliary membership from `P2`.
  have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
  -- An auxiliary open neighbourhood of `x`.
  let U : Set X := interior (closure (interior A))
  have hUx : x ∈ U := by
    simpa [U] using hxInt
  have hUopen : IsOpen U := by
    have : IsOpen (interior (closure (interior A))) := isOpen_interior
    simpa [U] using this
  have hUsubset : (U : Set X) ⊆ closure (interior A) := by
    have : (interior (closure (interior A)) : Set X) ⊆ closure (interior A) :=
      interior_subset
    simpa [U] using this
  -- Image of `U` through `f`.
  let V : Set Y := f '' U
  have hVopen : IsOpen V := by
    have hf : IsOpenMap f := f.isOpenMap
    have : IsOpen (f '' U) := hf _ hUopen
    simpa [V] using this
  have hyV : f x ∈ V := by
    dsimp [V]; exact ⟨x, hUx, rfl⟩
  -- Show that `V` is contained in the required closure.
  have hVsub : (V : Set Y) ⊆ closure (interior (f '' A)) := by
    intro z hz
    rcases hz with ⟨w, hwU, rfl⟩
    -- `w ∈ closure (interior A)`
    have hwCl : w ∈ closure (interior A) := hUsubset hwU
    -- Show `f w ∈ closure (interior (f '' A))`.
    have : f w ∈ closure (interior (f '' A)) := by
      -- Use the neighbourhood characterization of the closure.
      apply (mem_closure_iff).2
      intro W hWopen hfwW
      -- Pull `W` back via `f`.
      have hPreOpen : IsOpen (f ⁻¹' W) := hWopen.preimage f.continuous
      have hwPre : w ∈ f ⁻¹' W := by
        simpa [Set.mem_preimage] using hfwW
      -- `w` is in the closure of `interior A`, hence the intersection is non-empty.
      have hNonempty :
          ((f ⁻¹' W) ∩ interior A).Nonempty :=
        (mem_closure_iff).1 hwCl (f ⁻¹' W) hPreOpen hwPre
      rcases hNonempty with ⟨u, huPre, huIntA⟩
      -- Map the witness back to `Y`.
      have hfuW : f u ∈ W := by
        have : u ∈ f ⁻¹' W := huPre
        simpa [Set.mem_preimage] using this
      -- `f u` lies in `interior (f '' A)`.
      have hfuInt : f u ∈ interior (f '' A) := by
        -- `f '' interior A` is open.
        have hOpen_fint : IsOpen (f '' interior A) := by
          have hf : IsOpenMap f := f.isOpenMap
          simpa using hf _ isOpen_interior
        -- Inclusion into `f '' A`.
        have hSub : (f '' interior A : Set Y) ⊆ f '' A := by
          intro v hv
          rcases hv with ⟨t, htInt, rfl⟩
          exact ⟨t, interior_subset htInt, rfl⟩
        have hSubInt :
            (f '' interior A : Set Y) ⊆ interior (f '' A) :=
          interior_maximal hSub hOpen_fint
        have : f u ∈ f '' interior A := ⟨u, huIntA, rfl⟩
        exact hSubInt this
      exact ⟨f u, ⟨hfuW, hfuInt⟩⟩
    exact this
  -- `V` is an open neighbourhood of `f x` contained in the desired set,
  -- hence `f x` belongs to the required interior.
  have hNhd : (V : Set Y) ∈ 𝓝 (f x) := hVopen.mem_nhds hyV
  have hNhd' :
      (closure (interior (f '' A)) : Set Y) ∈ 𝓝 (f x) :=
    Filter.mem_of_superset hNhd hVsub
  have h_mem :
      f x ∈ interior (closure (interior (f '' A))) :=
    (mem_interior_iff_mem_nhds).2 hNhd'
  simpa using h_mem

theorem P1_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ Y) {B : Set Y} : P1 B → P1 (f ⁻¹' B) := by
  intro hP1B
  -- Transfer the property through the inverse homeomorphism.
  have hP1_pre : P1 ((f.symm) '' B) :=
    P1_image_homeomorph (f := f.symm) hP1B
  -- Identify the image with the preimage.
  have hEq : ((f.symm) '' B : Set X) = f ⁻¹' B := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hyB, rfl⟩
      show f (f.symm y) ∈ B
      simpa using hyB
    · intro hx
      have hfxB : f x ∈ B := by
        simpa [Set.mem_preimage] using hx
      exact
        ⟨f x, hfxB, by
          simpa using (f.symm_apply_apply x)⟩
  -- Establish `P1` for the preimage.
  intro x hx
  have hx' : x ∈ ((f.symm) '' B) := by
    simpa [hEq] using hx
  have h_cl : x ∈ closure (interior ((f.symm) '' B)) := hP1_pre hx'
  simpa [hEq] using h_cl

theorem P3_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ Y) {B : Set Y} : P3 B → P3 (f ⁻¹' B) := by
  intro hP3B
  intro x hx
  -- `hx` gives `f x ∈ B`.
  have hfxB : f x ∈ B := by
    simpa [Set.mem_preimage] using hx
  -- Apply `P3 B`.
  have hfxInt : f x ∈ interior (closure B) := hP3B hfxB
  -- Auxiliary open set in `Y`.
  set V : Set Y := interior (closure B) with hVdef
  have hVopen : IsOpen V := by
    simpa [hVdef] using isOpen_interior
  have hfxV : f x ∈ V := by
    simpa [hVdef] using hfxInt
  -- Pull the open set back to `X`.
  set U : Set X := f ⁻¹' V with hUdef
  have hUopen : IsOpen U := by
    have : IsOpen (f ⁻¹' V) := hVopen.preimage f.continuous
    simpa [hUdef] using this
  have hxU : x ∈ U := by
    simpa [hUdef, Set.mem_preimage] using hfxV
  -- Show that every point of `U` lies in the closure of `f ⁻¹' B`.
  have hU_sub : (U : Set X) ⊆ closure (f ⁻¹' B) := by
    intro y hyU
    -- `f y` lies in `V ⊆ closure B`.
    have hfyV : f y ∈ V := by
      simpa [hUdef, Set.mem_preimage] using hyU
    have hfy_clB : f y ∈ closure B := by
      have hVsubset : (V : Set Y) ⊆ closure B := by
        intro z hz
        exact interior_subset hz
      exact hVsubset hfyV
    -- Prove that `y` belongs to the closure of `f ⁻¹' B`.
    have : y ∈ closure (f ⁻¹' B) := by
      -- Use the neighbourhood characterization of closure.
      apply (mem_closure_iff).2
      intro W hWopen hyW
      -- The image of `W` under `f` is an open neighbourhood of `f y`.
      have hWimageOpen : IsOpen (f '' W) := by
        have hf : IsOpenMap f := f.isOpenMap
        simpa using hf W hWopen
      have hfyW : f y ∈ f '' W := by
        exact ⟨y, hyW, rfl⟩
      -- Because `f y` is in the closure of `B`, the intersection is nonempty.
      have hNonempty : ((f '' W) ∩ B).Nonempty :=
        (mem_closure_iff).1 hfy_clB _ hWimageOpen hfyW
      rcases hNonempty with ⟨z, hzFW, hzB⟩
      rcases hzFW with ⟨w, hwW, hw_eq⟩
      -- `w` witnesses the required intersection in `X`.
      have hwB : w ∈ f ⁻¹' B := by
        have : f w ∈ B := by
          simpa [hw_eq] using hzB
        simpa [Set.mem_preimage] using this
      exact ⟨w, hwW, hwB⟩
    exact this
  -- Use `U` to witness that `x` is in the interior of the closure.
  have hNhd : (U : Set X) ∈ 𝓝 x := hUopen.mem_nhds hxU
  have hNhd' : (closure (f ⁻¹' B) : Set X) ∈ 𝓝 x :=
    Filter.mem_of_superset hNhd hU_sub
  have h_mem : x ∈ interior (closure (f ⁻¹' B)) :=
    (mem_interior_iff_mem_nhds).2 hNhd'
  simpa using h_mem

theorem P2_of_P3_and_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : P3 A → P1 A → P2 A := by
  intro hP3 hP1 x hxA
  -- From `P1` we get the equality of the two closures.
  have h_closure_eq : closure (interior (A : Set X)) = closure A :=
    closure_interior_eq_of_P1 (A := A) hP1
  -- Apply `P3` to obtain membership in the interior of `closure A`.
  have hx_int : x ∈ interior (closure A) := hP3 hxA
  -- Rewrite using the closure equality.
  simpa [h_closure_eq] using hx_int

theorem P3_iff_P2_of_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} : closure A = closure (interior A) → (P3 A ↔ P2 A) := by
  intro hEq
  refine ⟨?forward, ?backward⟩
  · intro hP3
    intro x hxA
    have hx_int : x ∈ interior (closure A) := hP3 hxA
    simpa [hEq] using hx_int
  · intro hP2
    exact P2_to_P3 (A := A) hP2

theorem P1_complement_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → P1 (Aᶜ) := by
  intro hClosed
  have hOpen : IsOpen (Aᶜ : Set X) := hClosed.isOpen_compl
  exact P1_of_open (A := Aᶜ) hOpen

theorem P3_preimage_open {X : Type*} [TopologicalSpace X] {A B : Set X} : IsOpen B → P3 A → P3 (A ∩ B) := by
  intro hBOpen hP3
  intro x hx
  rcases hx with ⟨hxA, hxB⟩
  -- `x` is in the interior of `closure A`
  have hxInt : x ∈ interior (closure A) := hP3 hxA
  -- Auxiliary open neighbourhood around `x`
  set O : Set X := interior (closure A) ∩ B with hOdef
  have hOopen : IsOpen O := by
    have : IsOpen (interior (closure A)) := isOpen_interior
    simpa [hOdef] using this.inter hBOpen
  have hxO : x ∈ O := by
    dsimp [O, hOdef]
    exact ⟨hxInt, hxB⟩
  -- `O` is contained in the closure of `A ∩ B`
  have hOsubset : (O : Set X) ⊆ closure (A ∩ B) := by
    intro y hyO
    rcases hyO with ⟨hyInt, hyB⟩
    have hyClA : y ∈ closure (A : Set X) := interior_subset hyInt
    -- Show `y ∈ closure (A ∩ B)`
    have : y ∈ closure (A ∩ B) := by
      refine (mem_closure_iff).2 ?_
      intro U hUopen hyU
      have hVopen : IsOpen (U ∩ B) := hUopen.inter hBOpen
      have hyV : y ∈ U ∩ B := ⟨hyU, hyB⟩
      have hNonempty : ((U ∩ B) ∩ A).Nonempty :=
        (mem_closure_iff).1 hyClA (U ∩ B) hVopen hyV
      rcases hNonempty with ⟨z, ⟨⟨hzU, hzB⟩, hzA⟩⟩
      exact ⟨z, hzU, ⟨hzA, hzB⟩⟩
    exact this
  -- Use `O` to witness membership in the required interior
  have hNhd : (O : Set X) ∈ 𝓝 x := hOopen.mem_nhds hxO
  have hMem : x ∈ interior (closure (A ∩ B)) :=
    (mem_interior_iff_mem_nhds).2 (Filter.mem_of_superset hNhd hOsubset)
  simpa using hMem

theorem P3_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P3 (interior (closure A)) := by
  exact P3_of_open (A := interior (closure A)) isOpen_interior

theorem P1_homeomorph_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ Y) {A : Set X} : P1 A ↔ P1 (f '' A) := by
  constructor
  · intro hP1A
    exact P1_image_homeomorph (f := f) hP1A
  · intro hP1Image
    -- Pull back the property along `f`.
    have hPre : P1 (f ⁻¹' (f '' A)) :=
      P1_preimage_homeomorph (f := f) hP1Image
    -- Identify the pulled–back set with `A`.
    have hEq : (f ⁻¹' (f '' A) : Set X) = A := by
      ext x
      constructor
      · intro hx
        have hfx : f x ∈ f '' A := by
          simpa [Set.mem_preimage] using hx
        rcases hfx with ⟨a, haA, hfa⟩
        have haeq : a = x := by
          apply f.injective
          simpa using hfa
        simpa [haeq] using haA
      · intro hxA
        have : f x ∈ f '' A := ⟨x, hxA, rfl⟩
        simpa [Set.mem_preimage] using this
    simpa [hEq] using hPre

theorem P2_homeomorph_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ Y) {A : Set X} : P2 A ↔ P2 (f '' A) := by
  constructor
  · intro hP2A
    exact P2_image_homeomorph (f := f) hP2A
  · intro hP2Image
    -- Pull the property back along `f`.
    have hPre : P2 (f ⁻¹' (f '' A)) :=
      P2_preimage_homeomorph (f := f) hP2Image
    -- Identify the pulled-back set with `A`.
    have hEq : (f ⁻¹' (f '' A) : Set X) = A := by
      ext x
      constructor
      · intro hx
        -- `hx` says `f x ∈ f '' A`.
        have hfx : f x ∈ f '' A := by
          simpa [Set.mem_preimage] using hx
        rcases hfx with ⟨a, haA, hfa⟩
        -- Use injectivity to show `a = x`.
        have hax : a = x := by
          apply f.injective
          simpa using hfa
        simpa [hax] using haA
      · intro hxA
        -- Show `f x ∈ f '' A`, hence the preimage condition.
        have hfx : f x ∈ f '' A := ⟨x, hxA, rfl⟩
        simpa [Set.mem_preimage] using hfx
    simpa [hEq] using hPre

theorem P3_homeomorph_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ Y) {A : Set X} : P3 A ↔ P3 (f '' A) := by
  constructor
  · intro hP3A
    -- Transport the property along `f.symm`.
    have hPre : P3 (f.symm ⁻¹' A) :=
      P3_preimage_homeomorph (f := f.symm) hP3A
    -- Identify the transported set with `f '' A`.
    have hEq : (f.symm ⁻¹' A : Set Y) = f '' A := by
      ext y
      constructor
      · intro hy
        have hAy : f.symm y ∈ A := by
          simpa using hy
        exact
          ⟨f.symm y, hAy, by
            simpa using (f.apply_symm_apply y)⟩
      · rintro ⟨x, hxA, rfl⟩
        simpa using hxA
    simpa [hEq] using hPre
  · intro hP3Image
    -- Pull the property back along `f`.
    have hPre : P3 (f ⁻¹' (f '' A)) :=
      P3_preimage_homeomorph (f := f) hP3Image
    -- Identify the pulled–back set with `A`.
    have hEq : (f ⁻¹' (f '' A) : Set X) = A := by
      ext x
      constructor
      · intro hx
        have hfx : f x ∈ f '' A := by
          simpa [Set.mem_preimage] using hx
        rcases hfx with ⟨a, haA, hfa⟩
        have hax : a = x := by
          apply f.injective
          simpa using hfa
        simpa [hax] using haA
      · intro hxA
        have hfx : f x ∈ f '' A := ⟨x, hxA, rfl⟩
        simpa [Set.mem_preimage] using hfx
    simpa [hEq] using hPre

theorem P3_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ Y) {A : Set X} : P3 A → P3 (f '' A) := (P3_homeomorph_iff (f := f) (A := A)).1

theorem P1_inter_open {X : Type*} [TopologicalSpace X] {A B : Set X} : IsOpen B → P1 A → P1 (A ∩ B) := by
  intro hBopen hP1
  intro x hx
  rcases hx with ⟨hxA, hxB⟩
  -- Use the neighbourhood characterization of the closure.
  apply (mem_closure_iff).2
  intro V hVopen hxV
  -- `V ∩ B` is an open neighbourhood of `x`.
  have hVBopen : IsOpen (V ∩ B) := hVopen.inter hBopen
  have hxVB : x ∈ V ∩ B := ⟨hxV, hxB⟩
  -- From `P1 A`, we know `x ∈ closure (interior A)`.
  have hx_cl : x ∈ closure (interior A) := hP1 hxA
  -- Hence `(V ∩ B) ∩ interior A` is non-empty.
  have hNonempty : ((V ∩ B) ∩ interior A).Nonempty :=
    (mem_closure_iff).1 hx_cl (V ∩ B) hVBopen hxVB
  rcases hNonempty with ⟨y, ⟨hyV, hyB⟩, hyIntA⟩
  -- Show that `y ∈ interior (A ∩ B)`.
  have hyIntAB : y ∈ interior (A ∩ B) := by
    -- `interior A ∩ B` is an open subset of `A ∩ B`.
    have hSub : (interior A ∩ B : Set X) ⊆ interior (A ∩ B) := by
      have hOpen : IsOpen (interior A ∩ B) := isOpen_interior.inter hBopen
      have hIncl : (interior A ∩ B : Set X) ⊆ A ∩ B := by
        intro z hz
        rcases hz with ⟨hzIntA, hzB⟩
        exact ⟨interior_subset hzIntA, hzB⟩
      exact interior_maximal hIncl hOpen
    exact hSub ⟨hyIntA, hyB⟩
  -- Provide the required intersection with the interior.
  exact ⟨y, hyV, hyIntAB⟩

theorem P2_compl_closed {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → P2 (Aᶜ) := by
  intro hClosed
  simpa using P2_of_open (A := Aᶜ) hClosed.isOpen_compl

theorem P1_prod_symm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P1 (Set.prod A B) → P1 (Set.prod B A) := by
  intro hP1
  -- Transport `P1` through the coordinate‐swap homeomorphism.
  have hImage :
      P1
        ((fun a : X × Y => Prod.swap a) '' (Set.prod A B) : Set (Y × X)) := by
    simpa using
      (P1_image_homeomorph (f := Homeomorph.prodComm X Y) hP1)
  -- The image of `A × B` under the swap map is `B × A`.
  have hImageEq :
      ((fun a : X × Y => Prod.swap a) '' (Set.prod A B) : Set (Y × X)) =
        Set.prod B A := by
    ext p
    constructor
    · -- forward direction
      rintro ⟨q, ⟨hqA, hqB⟩, rfl⟩
      exact ⟨hqB, hqA⟩
    · -- reverse direction
      rintro ⟨hpB, hpA⟩
      refine ⟨Prod.swap p, ?_, ?_⟩
      · exact ⟨hpA, hpB⟩
      ·
        cases p with
        | mk y x =>
            simp [Prod.swap]        -- evaluates the swap
  -- Reinterpret `hImage` via the identified equality.
  simpa [hImageEq] using hImage

theorem P2_inter_open {X : Type*} [TopologicalSpace X] {A B : Set X} : IsOpen B → P2 A → P2 (A ∩ B) := by
  intro hBopen hP2
  intro x hx
  rcases hx with ⟨hxA, hxB⟩
  -- From `P2 A`, obtain a neighbourhood of `x`.
  have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
  -- Auxiliary open set around `x`.
  set O : Set X := interior (closure (interior A)) ∩ B with hOdef
  have hOopen : IsOpen O := by
    have : IsOpen (interior (closure (interior A))) := isOpen_interior
    have : IsOpen (interior (closure (interior A)) ∩ B) :=
      this.inter hBopen
    simpa [hOdef] using this
  have hxO : x ∈ O := by
    dsimp [O, hOdef]
    exact ⟨hxInt, hxB⟩
  -- Show that `O` is contained in the relevant closure.
  have hOsubset : (O : Set X) ⊆ closure (interior (A ∩ B)) := by
    intro y hyO
    rcases hyO with ⟨hyIntClA, hyB⟩
    have hyClA : y ∈ closure (interior A) := interior_subset hyIntClA
    -- Prove `y ∈ closure (interior (A ∩ B))`.
    have : y ∈ closure (interior (A ∩ B)) := by
      apply (mem_closure_iff).2
      intro V hVopen hyV
      -- Refine the neighbourhood with `B`.
      have hVBopen : IsOpen (V ∩ B) := hVopen.inter hBopen
      have hyVB : y ∈ V ∩ B := ⟨hyV, hyB⟩
      -- Use closeness to hit `interior A`.
      have hNonempty : ((V ∩ B) ∩ interior A).Nonempty :=
        (mem_closure_iff).1 hyClA (V ∩ B) hVBopen hyVB
      rcases hNonempty with ⟨z, ⟨hzV, hzB⟩, hzIntA⟩
      -- Show the witness lies in `interior (A ∩ B)`.
      have hzIntAB : z ∈ interior (A ∩ B) := by
        -- The open set `interior A ∩ B` sits inside `A ∩ B`.
        have hSub : (interior A ∩ B : Set X) ⊆ interior (A ∩ B) := by
          have hOpen : IsOpen (interior A ∩ B) :=
            isOpen_interior.inter hBopen
          have hIncl : (interior A ∩ B : Set X) ⊆ A ∩ B := by
            intro w hw
            rcases hw with ⟨hwIntA, hwB⟩
            exact ⟨interior_subset hwIntA, hwB⟩
          exact interior_maximal hIncl hOpen
        exact hSub ⟨hzIntA, hzB⟩
      exact ⟨z, hzV, hzIntAB⟩
    exact this
  -- Conclude that `x` is in the desired interior.
  have hNhd : (O : Set X) ∈ 𝓝 x := hOopen.mem_nhds hxO
  have hMem : x ∈ interior (closure (interior (A ∩ B))) :=
    (mem_interior_iff_mem_nhds).2 (Filter.mem_of_superset hNhd hOsubset)
  simpa using hMem

theorem P2_union₂ {X : Type*} [TopologicalSpace X] {ι κ : Sort*} {A : ι → κ → Set X} : (∀ i j, P2 (A i j)) → P2 (⋃ i, ⋃ j, A i j) := by
  intro hAll
  -- First, establish `P2` for `⋃ j, A i j` for each fixed `i`.
  have hP2_i : ∀ i, P2 (⋃ j, A i j) := by
    intro i
    have hP2_ij : ∀ j, P2 (A i j) := by
      intro j
      exact hAll i j
    simpa using (P2_unionᵢ (A := fun j => A i j) hP2_ij)
  -- Then, use `P2_unionᵢ` once more to get the result for the double union.
  simpa using (P2_unionᵢ (A := fun i => ⋃ j, A i j) hP2_i)

theorem P1_interior_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → interior (closure (interior A)) = interior (closure A) := by
  intro hP1
  have hcl : closure (interior (A : Set X)) = closure A :=
    closure_interior_eq_of_P1 (A := A) hP1
  simpa [hcl]

theorem P2_inter {X : Type*} [TopologicalSpace X] {A B : Set X} : P2 A → P2 B → P2 (A ∩ B) := by
  intro hP2A hP2B x hx
  rcases hx with ⟨hxA, hxB⟩
  -- Auxiliary open neighbourhoods furnished by `P2 A` and `P2 B`.
  set UA : Set X := interior (closure (interior A)) with hUA
  set UB : Set X := interior (closure (interior B)) with hUB
  have hUA_open : IsOpen UA := by
    simpa [hUA] using (isOpen_interior :
      IsOpen (interior (closure (interior A))))
  have hUB_open : IsOpen UB := by
    simpa [hUB] using (isOpen_interior :
      IsOpen (interior (closure (interior B))))
  have hxUA : x ∈ UA := by
    have : x ∈ interior (closure (interior A)) := hP2A hxA
    simpa [hUA] using this
  have hxUB : x ∈ UB := by
    have : x ∈ interior (closure (interior B)) := hP2B hxB
    simpa [hUB] using this
  -- Combine the two neighbourhoods.
  have hO_open : IsOpen (UA ∩ UB : Set X) := hUA_open.inter hUB_open
  have hxO : x ∈ UA ∩ UB := ⟨hxUA, hxUB⟩
  -- Main claim: the intersection lies in the relevant closure.
  have hO_sub : (UA ∩ UB : Set X) ⊆ closure (interior (A ∩ B)) := by
    intro y hy
    rcases hy with ⟨hyUA, hyUB⟩
    -- `y` is simultaneously in the closures of `interior A` and `interior B`.
    have hy_clA : y ∈ closure (interior A) := by
      -- `UA ⊆ closure (interior A)`
      have hsub : (UA : Set X) ⊆ closure (interior A) := by
        intro z hz
        have hz' : z ∈ interior (closure (interior A)) := by
          simpa [hUA] using hz
        exact interior_subset hz'
      exact hsub hyUA
    have hy_clB : y ∈ closure (interior B) := by
      have hsub : (UB : Set X) ⊆ closure (interior B) := by
        intro z hz
        have hz' : z ∈ interior (closure (interior B)) := by
          simpa [hUB] using hz
        exact interior_subset hz'
      exact hsub hyUB
    -- Show that every open neighbourhood of `y` meets `interior (A ∩ B)`.
    have : y ∈ closure (interior (A ∩ B)) := by
      apply (mem_closure_iff).2
      intro V hVopen hyV
      -- First refinement, intersect with `UB`.
      have hV1_open : IsOpen (V ∩ UB) := hVopen.inter hUB_open
      have hyV1 : y ∈ V ∩ UB := ⟨hyV, hyUB⟩
      -- Obtain a point in `interior A`.
      rcases (mem_closure_iff).1 hy_clA (V ∩ UB) hV1_open hyV1 with
        ⟨a, ⟨haV, haUB⟩, haIntA⟩
      -- `a` is now in `V`, `UB`, and `interior A`.
      have ha_clB : a ∈ closure (interior B) := by
        have hsub : (UB : Set X) ⊆ closure (interior B) := by
          intro z hz
          have hz' : z ∈ interior (closure (interior B)) := by
            simpa [hUB] using hz
          exact interior_subset hz'
        exact hsub haUB
      -- Second refinement, intersect with `interior A`.
      have hW_open : IsOpen (V ∩ interior A) := hVopen.inter isOpen_interior
      have haW : a ∈ V ∩ interior A := ⟨haV, haIntA⟩
      -- Obtain a point in `interior B`.
      rcases (mem_closure_iff).1 ha_clB (V ∩ interior A) hW_open haW with
        ⟨z, ⟨hzV, hzIntA⟩, hzIntB⟩
      -- `z` lies in `V`, `interior A`, and `interior B`.
      have hzIntAB : z ∈ interior (A ∩ B) := by
        -- The set `interior A ∩ interior B` is open and contained in `A ∩ B`.
        have hS_open : IsOpen (interior A ∩ interior B) :=
          isOpen_interior.inter isOpen_interior
        have hS_sub : (interior A ∩ interior B : Set X) ⊆ A ∩ B := by
          intro w hw
          rcases hw with ⟨h1, h2⟩
          exact ⟨interior_subset h1, interior_subset h2⟩
        have hS_to : (interior A ∩ interior B : Set X) ⊆
            interior (A ∩ B) :=
          interior_maximal hS_sub hS_open
        have hzS : z ∈ interior A ∩ interior B := ⟨hzIntA, hzIntB⟩
        exact hS_to hzS
      exact ⟨z, hzV, hzIntAB⟩
    exact this
  -- Use the neighbourhood just constructed.
  have hNhd : (UA ∩ UB : Set X) ∈ 𝓝 x :=
    hO_open.mem_nhds hxO
  have h_mem :
      x ∈ interior (closure (interior (A ∩ B))) :=
    (mem_interior_iff_mem_nhds).2
      (Filter.mem_of_superset hNhd hO_sub)
  simpa using h_mem

theorem P3_prod_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : P3 A → P3 (Set.prod A (Set.univ : Set Y)) := by
  intro hP3A
  simpa using
    (P3_prod (A := A) (B := (Set.univ : Set Y)) hP3A (P3_univ (X := Y)))

theorem P3_prod_swap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P3 (Set.prod A B) → P3 (Set.prod B A) := by
  intro hP3
  -- Transport `P3` through the coordinate–swap homeomorphism.
  have hImage :
      P3
        ((fun a : X × Y => Prod.swap a) '' (Set.prod A B) : Set (Y × X)) := by
    simpa using
      (P3_image_homeomorph (f := Homeomorph.prodComm X Y) hP3)
  -- The image of `A × B` under the swap map is `B × A`.
  have hImageEq :
      ((fun a : X × Y => Prod.swap a) '' (Set.prod A B) : Set (Y × X)) =
        Set.prod B A := by
    ext p
    constructor
    · rintro ⟨q, ⟨hqA, hqB⟩, rfl⟩
      exact ⟨hqB, hqA⟩
    · rintro ⟨hpB, hpA⟩
      refine ⟨Prod.swap p, ?_, ?_⟩
      · exact ⟨hpA, hpB⟩
      · cases p with
        | mk y x =>
            simp [Prod.swap]
  simpa [hImageEq] using hImage

theorem P1_prod_four {W X Y Z : Type*} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set W} {B : Set X} {C : Set Y} {D : Set Z} : P1 A → P1 B → P1 C → P1 D → P1 (Set.prod (Set.prod (Set.prod A B) C) D) := by
  intro hP1A hP1B hP1C hP1D
  -- Combine `A` and `B`.
  have hP1AB : P1 (Set.prod A B) :=
    P1_prod (A := A) (B := B) hP1A hP1B
  -- Combine the result with `C`.
  have hP1ABC : P1 (Set.prod (Set.prod A B) C) :=
    P1_prod (A := Set.prod A B) (B := C) hP1AB hP1C
  -- Finally, combine with `D`.
  exact
    P1_prod (A := Set.prod (Set.prod A B) C) (B := D) hP1ABC hP1D

theorem P1_commute_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P1 (Set.prod A B) ↔ P1 (Set.prod B A) := by
  constructor
  · intro h
    exact P1_prod_symm (A := A) (B := B) h
  · intro h
    simpa using
      (P1_prod_symm (X := Y) (Y := X) (A := B) (B := A) h)

theorem P2_prod_comm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P2 (Set.prod A B) ↔ P2 (Set.prod B A) := by
  constructor
  · intro h
    -- Transport the property through the coordinate–swap homeomorphism.
    have hImage :
        P2
          ((fun a : X × Y => Prod.swap a) '' (Set.prod A B) : Set (Y × X)) := by
      simpa using
        (P2_image_homeomorph (f := Homeomorph.prodComm X Y) h)
    -- The image of `A × B` under the swap map is `B × A`.
    have hImageEq :
        ((fun a : X × Y => Prod.swap a) '' (Set.prod A B) : Set (Y × X)) =
          Set.prod B A := by
      ext p
      constructor
      · rintro ⟨q, ⟨hqA, hqB⟩, rfl⟩
        exact ⟨hqB, hqA⟩
      · rintro ⟨hpB, hpA⟩
        refine ⟨Prod.swap p, ?_, ?_⟩
        · exact ⟨hpA, hpB⟩
        · cases p with
          | mk y x =>
              simp [Prod.swap]
    simpa [hImageEq] using hImage
  · intro h
    -- Transport the property back through the inverse (same) homeomorphism.
    have hImage :
        P2
          ((fun a : Y × X => Prod.swap a) '' (Set.prod B A) : Set (X × Y)) := by
      simpa using
        (P2_image_homeomorph (f := Homeomorph.prodComm Y X) h)
    -- The image of `B × A` under the swap map is `A × B`.
    have hImageEq :
        ((fun a : Y × X => Prod.swap a) '' (Set.prod B A) : Set (X × Y)) =
          Set.prod A B := by
      ext p
      constructor
      · rintro ⟨q, ⟨hqB, hqA⟩, rfl⟩
        exact ⟨hqA, hqB⟩
      · rintro ⟨hpA, hpB⟩
        refine ⟨Prod.swap p, ?_, ?_⟩
        · exact ⟨hpB, hpA⟩
        · cases p with
          | mk x y =>
              simp [Prod.swap]
    simpa [hImageEq] using hImage

theorem P2_image_homeomorph_comp {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (f : X ≃ₜ Y) (g : Y ≃ₜ Z) {A : Set X} : P2 A → P2 ((g ∘ f) '' A) := by
  intro hP2A
  -- First, transport the property along `f`.
  have h1 : P2 (f '' A) :=
    (P2_image_homeomorph (f := f) (A := A)) hP2A
  -- Next, transport the property along `g`.
  have h2 : P2 (g '' (f '' A)) :=
    (P2_image_homeomorph (f := g) (A := f '' A)) h1
  -- Relate the iterated image to the image under the composition.
  have hEq : (g '' (f '' A) : Set Z) = ((g ∘ f) '' A) := by
    ext z
    constructor
    · rintro ⟨y, ⟨x, hxA, rfl⟩, rfl⟩
      exact ⟨x, hxA, rfl⟩
    · rintro ⟨x, hxA, rfl⟩
      exact ⟨f x, ⟨x, hxA, rfl⟩, rfl⟩
  -- Rewrite using the established equality.
  simpa [hEq] using h2

theorem P3_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} : P3 A → P3 B → P3 C → P3 (A ∪ B ∪ C) := by
  intro hA hB hC
  -- Establish `P3` for `A ∪ B`.
  have hAB : P3 (A ∪ B) := P3_union (A := A) (B := B) hA hB
  -- Combine with `C`.
  have hABC : P3 ((A ∪ B) ∪ C) := P3_union (A := A ∪ B) (B := C) hAB hC
  simpa [Set.union_assoc] using hABC

theorem P2_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : P2 A := by
  intro x hxA
  -- Any nonempty subset of a subsingleton type is the whole space.
  have hAuniv : (A : Set X) = Set.univ := by
    ext y
    constructor
    · intro _; exact Set.mem_univ y
    · intro _
      have h_eq : y = x := Subsingleton.elim _ _
      simpa [h_eq] using hxA
  -- With this identification the desired membership is immediate.
  simpa [hAuniv, interior_univ, closure_univ] using (Set.mem_univ x)

theorem P1_prod_five {V W X Y Z : Type*} [TopologicalSpace V] [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set V} {B : Set W} {C : Set X} {D : Set Y} {E : Set Z} : P1 A → P1 B → P1 C → P1 D → P1 E → P1 (Set.prod (Set.prod (Set.prod (Set.prod A B) C) D) E) := by
  intro hP1A hP1B hP1C hP1D hP1E
  -- First, obtain `P1` for the four–fold product `(A × B) × C × D`.
  have hP1ABCD :
      P1 (Set.prod (Set.prod (Set.prod A B) C) D) :=
    P1_prod_four (A := A) (B := B) (C := C) (D := D)
      hP1A hP1B hP1C hP1D
  -- Combine this with `E`.
  exact
    P1_prod
      (A := Set.prod (Set.prod (Set.prod A B) C) D)
      (B := E)
      hP1ABCD
      hP1E

theorem P2_union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X} : P2 A → P2 B → P2 C → P2 D → P2 (A ∪ B ∪ C ∪ D) := by
  intro hA hB hC hD
  -- Combine `A` and `B`.
  have hAB : P2 (A ∪ B) := P2_union hA hB
  -- Combine the result with `C`.
  have hABC : P2 ((A ∪ B) ∪ C) := P2_union hAB hC
  -- Finally, combine with `D`.
  have hABCD : P2 (((A ∪ B) ∪ C) ∪ D) := P2_union hABC hD
  simpa [Set.union_assoc] using hABCD

theorem P1_prod_assoc {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : P1 (Set.prod A (Set.prod B C)) ↔ P1 (Set.prod (Set.prod A B) C) := by
  -- The associator homeomorphism, oriented so that it sends `(x , (y , z))`
  -- to `((x , y) , z)`.
  let f : X × (Y × Z) ≃ₜ (X × Y) × Z := (Homeomorph.prodAssoc X Y Z).symm
  -- First, identify the image of `A × (B × C)` under `f`.
  have hImage :
      (f '' (Set.prod A (Set.prod B C)) : Set ((X × Y) × Z)) =
        Set.prod (Set.prod A B) C := by
    ext p
    constructor
    · -- Forward direction.
      rintro ⟨q, hq, rfl⟩
      rcases q with ⟨x, yz⟩
      rcases yz with ⟨y, z⟩
      rcases hq with ⟨hxA, hYZ⟩
      rcases hYZ with ⟨hyB, hzC⟩
      -- After unfolding, everything is by `simp`.
      simp [f, Homeomorph.prodAssoc, Set.prod, hxA, hyB, hzC]
    · -- Reverse direction.
      intro hp
      rcases p with ⟨⟨x, y⟩, z⟩
      rcases hp with ⟨hxy, hzC⟩
      rcases hxy with ⟨hxA, hyB⟩
      -- Build a preimage point.
      let q : X × (Y × Z) := (x, (y, z))
      have hq : q ∈ Set.prod A (Set.prod B C) := by
        dsimp [Set.prod, q]
        exact And.intro hxA (And.intro hyB hzC)
      refine ⟨q, hq, ?_⟩
      simp [q, f, Homeomorph.prodAssoc]
  -- Transport `P1` via the homeomorphism and rewrite with `hImage`.
  simpa [hImage] using
    (P1_homeomorph_iff (f := f) (A := Set.prod A (Set.prod B C)))

theorem P2_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} : P2 A → P2 B → P2 C → P2 (A ∪ B ∪ C) := by
  intro hA hB hC
  have hAB : P2 (A ∪ B) := P2_union (A := A) (B := B) hA hB
  have hABC : P2 ((A ∪ B) ∪ C) :=
    P2_union (A := (A ∪ B)) (B := C) hAB hC
  simpa [Set.union_assoc] using hABC

theorem P1_iff_P2_of_closure_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hDense : closure A = Set.univ) : P1 A ↔ P2 A := by
  refine ⟨?forward, ?backward⟩
  · intro hP1
    -- First, `hP1` gives equality of the two closures.
    have h_cl_eq : closure (interior (A : Set X)) = closure A :=
      closure_interior_eq_of_P1 (A := A) hP1
    -- Using the density assumption, this closure is all of `univ`.
    have h_cl_univ : closure (interior A) = Set.univ := by
      simpa [hDense] using h_cl_eq
    -- From this density we know `P2 A ↔ P3 A`.
    have h_equiv : P2 A ↔ P3 A :=
      (P2_iff_P3_of_interior_dense (A := A)) h_cl_univ
    -- And `P3 A` holds because `closure A = univ`.
    have hP3 : P3 A := P3_of_dense (A := A) hDense
    -- Hence `P2 A`.
    exact (h_equiv.2) hP3
  · intro hP2
    exact P2_to_P1 (A := A) hP2

theorem P2_prod_inf {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A₁ A₂ : Set X} {B₁ B₂ : Set Y} : P2 A₁ → P2 A₂ → P2 B₁ → P2 B₂ → P2 (Set.prod (A₁ ∩ A₂) (B₁ ∪ B₂)) := by
  intro hP2A₁ hP2A₂ hP2B₁ hP2B₂
  -- `P2` for the intersection of `A₁` and `A₂`
  have hA : P2 (A₁ ∩ A₂) := P2_inter (A := A₁) (B := A₂) hP2A₁ hP2A₂
  -- `P2` for the union of `B₁` and `B₂`
  have hB : P2 (B₁ ∪ B₂) := P2_union (A := B₁) (B := B₂) hP2B₁ hP2B₂
  -- Combine via the product lemma
  exact P2_prod (A := A₁ ∩ A₂) (B := B₁ ∪ B₂) hA hB

theorem P3_interior_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P3 (interior A) → P3 (interior B) → P3 (interior (A ∪ B)) := by
  intro _ _
  exact P3_of_open (A := interior (A ∪ B)) isOpen_interior

theorem P2_compl_compl {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A ↔ P2 (Aᶜᶜ) := by
  simpa [compl_compl] using (Iff.rfl : P2 A ↔ P2 A)

theorem P1_of_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : P1 A := by
  intro x hxA
  -- Any nonempty subset of a subsingleton type is the whole space.
  have hAuniv : (A : Set X) = Set.univ := by
    ext y
    constructor
    · intro _; exact Set.mem_univ y
    · intro _
      have : y = x := Subsingleton.elim _ _
      simpa [this] using hxA
  -- The desired claim follows after rewriting with `hAuniv`.
  simpa [hAuniv, interior_univ, closure_univ] using (Set.mem_univ x)

theorem P1_prod_union_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B C : Set Y} : P1 A → P1 B → P1 C → P1 (Set.prod A (B ∪ C)) := by
  intro hP1A hP1B hP1C
  have hP1BC : P1 (B ∪ C) := P1_union (A := B) (B := C) hP1B hP1C
  exact
    P1_prod (X := X) (Y := Y) (A := A) (B := B ∪ C) hP1A hP1BC

theorem P2_iff_P1_of_regular {X : Type*} [TopologicalSpace X] [T1Space X] {A : Set X} : (∀ x ∈ A, ∃ U, IsOpen U ∧ x ∈ U ∧ closure U ⊆ interior A) → (P2 A ↔ P1 A) := by
  intro hReg
  refine ⟨?forward, ?backward⟩
  · intro hP2
    exact P2_to_P1 (A := A) hP2
  · intro _hP1
    intro x hxA
    rcases hReg x hxA with ⟨U, hUopen, hxU, hClosureU⟩
    -- `U` is contained in `closure (interior A)`
    have hUsubset : (U : Set X) ⊆ closure (interior A) := by
      intro y hyU
      have hy_closureU : y ∈ closure U := subset_closure hyU
      have hy_intA : y ∈ interior A := hClosureU hy_closureU
      exact subset_closure hy_intA
    -- hence `x` lies in the interior of that closure
    have : x ∈ interior (closure (interior A)) := by
      have hNhd : (U : Set X) ∈ 𝓝 x := hUopen.mem_nhds hxU
      exact (mem_interior_iff_mem_nhds).2
        (Filter.mem_of_superset hNhd hUsubset)
    exact this

theorem P2_prod_of_empty {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : P2 A → P2 (Set.prod A (∅ : Set Y)) := by
  intro _ p hp
  cases hp.2

theorem P1_induction_on_closure {X : Type*} [TopologicalSpace X] {A : Set X} : (∀ x, x ∈ closure A → ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ closure (interior A)) → P1 A := by
  intro h x hxA
  have hx_cl : (x : X) ∈ closure (A : Set X) := subset_closure hxA
  rcases h x hx_cl with ⟨U, _hUopen, hxU, hUsubset⟩
  exact hUsubset hxU

theorem P2_unionᵢ_finset {X : Type*} [TopologicalSpace X] {ι : Type*} [Fintype ι] {A : ι → Set X} : (∀ i, P2 (A i)) → P2 (⋃ i, A i) := by
  intro hP2
  simpa using (P2_unionᵢ (A := A) hP2)

theorem P2_transfinite_union {X : Type*} [TopologicalSpace X] {ι : Type*} [Preorder ι] {A : ι → Set X} (hmon : ∀ i j, i ≤ j → A i ⊆ A j) : (∀ i, P2 (A i)) → P2 (⋃ i, A i) := by
  intro hP2
  simpa using (P2_unionᵢ (A := A) hP2)

theorem P2_Union_closed {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} : (∀ i, IsClosed (A i)) → (∀ i, P2 (A i)) → P2 (⋃ i, A i) := by
  intro _ hP2
  simpa using (P2_unionᵢ (A := A) hP2)

theorem P3_empty_iff {X : Type*} [TopologicalSpace X] {A : Set X} : A = ∅ → (P3 A ↔ True) := by
  intro hA
  have hP3 : P3 A := by
    simpa [hA] using (P3_empty (X := X))
  simpa using (iff_true_intro hP3)

theorem P1_Union₂ {X : Type*} [TopologicalSpace X] {ι κ : Sort*} {A : ι → κ → Set X} : (∀ i j, P1 (A i j)) → P1 (⋃ i, ⋃ j, A i j) := by
  intro hAll
  -- First, establish `P1` for `⋃ j, A i j` for each fixed `i`.
  have hP1_i : ∀ i, P1 (⋃ j, A i j) := by
    intro i
    have hP1_ij : ∀ j, P1 (A i j) := fun j => hAll i j
    simpa using (P1_unionᵢ (A := fun j => A i j) hP1_ij)
  -- Then, use `P1_unionᵢ` once more to get the result for the double union.
  simpa using (P1_unionᵢ (A := fun i => ⋃ j, A i j) hP1_i)

theorem P3_sigma_swap {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] {A : ∀ i, Set (X i)} : (∀ i, P3 (A i)) → P3 {p : Σ i, X i | P3 (A p.1) ∧ True} := by
  intro hAll
  -- Show the defining set is the whole space.
  have h_eq :
      ({p : Sigma X | P3 (A p.1) ∧ True} : Set (Sigma X)) = Set.univ := by
    ext p
    constructor
    · intro _
      exact Set.mem_univ _
    · intro _
      exact And.intro (hAll p.1) trivial
  -- Conclude using `P3_univ`.
  simpa [h_eq.symm] using (P3_univ (X := Sigma X))