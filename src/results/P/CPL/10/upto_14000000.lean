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


theorem closure_interior_eq_of_P2 {A : Set X} (h : P2 A) : closure (interior A) = closure A := by
  apply le_antisymm
  ·
    exact closure_mono interior_subset
  ·
    -- First, upgrade the hypothesis `h` to `A ⊆ closure (interior A)`
    have hA : (A : Set X) ⊆ closure (interior A) := by
      intro x hx
      have : x ∈ interior (closure (interior A)) := h hx
      exact interior_subset this
    -- Then take closures of both sides
    have : closure A ⊆ closure (interior A) := by
      simpa [closure_closure] using (closure_mono hA)
    exact this

theorem P1_union {A B : Set X} (hA : P1 A) (hB : P1 B) : P1 (A ∪ B) := by
  unfold P1 at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hxA' : x ∈ closure (interior A) := hA hxA
      have h_subset : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono
          (interior_mono
            (Set.subset_union_left : (A : Set X) ⊆ A ∪ B))
      exact h_subset hxA'
  | inr hxB =>
      have hxB' : x ∈ closure (interior B) := hB hxB
      have h_subset : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono
          (interior_mono
            (Set.subset_union_right : (B : Set X) ⊆ A ∪ B))
      exact h_subset hxB'

theorem exists_P1_P2_P3 : ∃ (A : Set X), P1 A ∧ P2 A ∧ P3 A := by
  refine ⟨(∅ : Set X), ?_, ?_, ?_⟩
  all_goals
    intro x hx
    cases hx

theorem P1_self_closure_interior {A : Set X} : P1 (closure (interior A)) := by
  -- Unfold the definition of `P1`
  unfold P1
  intro x hx
  -- First, show `interior A ⊆ interior (closure (interior A))`
  have h_interior_subset :
      (interior A : Set X) ⊆ interior (closure (interior A)) := by
    -- `interior_mono` gives the desired inclusion after noting
    -- `interior A ⊆ closure (interior A)`
    have h :
        interior (interior A) ⊆ interior (closure (interior A)) :=
      interior_mono (by
        intro y hy
        exact subset_closure hy)
    -- Since `interior (interior A) = interior A`, we rewrite
    simpa [isOpen_interior.interior_eq] using h
  -- Take closures of both sides of the inclusion obtained above
  have h_closure_subset :
      closure (interior A) ⊆ closure (interior (closure (interior A))) :=
    closure_mono h_interior_subset
  -- Apply the inclusion to the given element
  exact h_closure_subset hx

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P2 A) : Topology.P3 A := by
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := h hx
  have hsubset : (interior (closure (interior A)) : Set X) ⊆ interior (closure A) := by
    apply interior_mono
    exact closure_mono interior_subset
  exact hsubset hx'

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P2 A) : Topology.P1 A := by
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := h hx
  exact interior_subset hx'

theorem P1_of_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P1 A) : Topology.P1 (closure A) := by
  intro x hx
  -- First inclusion: `closure A ⊆ closure (interior A)`
  have h₁ : (closure A : Set X) ⊆ closure (interior A) := by
    have hA : (A : Set X) ⊆ closure (interior A) := h
    simpa [closure_closure] using closure_mono hA
  -- Second inclusion: `closure (interior A) ⊆ closure (interior (closure A))`
  have h₂ : (closure (interior A) : Set X) ⊆ closure (interior (closure A)) := by
    exact
      closure_mono
        (interior_mono (subset_closure : (A : Set X) ⊆ closure A))
  exact h₂ (h₁ hx)

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P2 A) (hB : Topology.P2 B) : Topology.P2 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x` is in `A`
      have hxA' : x ∈ interior (closure (interior A)) := hA hxA
      -- Show the bigger set contains the smaller one
      have hsubset :
          (interior (closure (interior A)) : Set X) ⊆
            interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        apply closure_mono
        apply interior_mono
        exact (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      exact hsubset hxA'
  | inr hxB =>
      -- `x` is in `B`
      have hxB' : x ∈ interior (closure (interior B)) := hB hxB
      have hsubset :
          (interior (closure (interior B)) : Set X) ⊆
            interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        apply closure_mono
        apply interior_mono
        exact (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      exact hsubset hxB'

theorem P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 (interior A) := by
  intro x hx
  -- `interior A` is open and contained in its closure, hence contained in the
  -- interior of that closure
  have hsubset : (interior A : Set X) ⊆ interior (closure (interior A)) := by
    apply interior_maximal
    · intro y hy
      exact subset_closure hy
    · exact isOpen_interior
  -- Apply the inclusion to the given element
  have : x ∈ interior (closure (interior A)) := hsubset hx
  -- Rewriting `interior (interior A)` to `interior A`
  simpa [isOpen_interior.interior_eq] using this

theorem P1_univ {X : Type*} [TopologicalSpace X] : Topology.P1 (Set.univ : Set X) := by
  intro x hx
  have hx_int : x ∈ interior (Set.univ : Set X) := by
    simpa [isOpen_univ.interior_eq] using hx
  have hx_closure : x ∈ closure (interior (Set.univ : Set X)) :=
    subset_closure hx_int
  simpa using hx_closure

theorem P2_empty {X : Type*} [TopologicalSpace X] : Topology.P2 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P3_empty {X : Type*} [TopologicalSpace X] : Topology.P3 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P3 A) (hB : Topology.P3 B) : Topology.P3 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x` belongs to `A`
      have hxA' : x ∈ interior (closure A) := hA hxA
      -- Show the required inclusion of interiors of closures
      have hsubset :
          (interior (closure A) : Set X) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        apply closure_mono
        exact (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      exact hsubset hxA'
  | inr hxB =>
      -- `x` belongs to `B`
      have hxB' : x ∈ interior (closure B) := hB hxB
      have hsubset :
          (interior (closure B) : Set X) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        apply closure_mono
        exact (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      exact hsubset hxB'

theorem exists_nonempty_P1 {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ A : Set X, A.Nonempty ∧ Topology.P1 A := by
  classical
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  ·
    rcases ‹Nonempty X› with ⟨x⟩
    exact ⟨x, by simp⟩
  ·
    simpa using Topology.P1_univ

theorem P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P3 A := by
  intro x hx
  exact (interior_maximal subset_closure hA) hx

theorem P1_preimage_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) {U : Set Y} (hU : IsOpen U) : Topology.P1 (f ⁻¹' U) := by
  intro x hx
  -- The preimage of an open set is open
  have h_open : IsOpen (f ⁻¹' U) := hU.preimage hf
  -- Hence its interior is itself
  have h_int_eq : interior (f ⁻¹' U) = f ⁻¹' U := h_open.interior_eq
  -- So `x` lies in the interior
  have hx_int : x ∈ interior (f ⁻¹' U) := by
    simpa [h_int_eq] using hx
  -- Therefore `x` is in the closure of the interior
  exact subset_closure hx_int

theorem exists_compact_P1 {X : Type*} [TopologicalSpace X] : ∃ K : Set X, IsCompact K ∧ Topology.P1 K := by
  refine ⟨(∅ : Set X), isCompact_empty, ?_⟩
  intro x hx
  cases hx

theorem P1_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {F : ι → Set X} (hF : ∀ i, Topology.P1 (F i)) : Topology.P1 (⋃ i, F i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxFi⟩
  have hxi : x ∈ closure (interior (F i)) := hF i hxFi
  have hsubset :
      (closure (interior (F i)) : Set X) ⊆ closure (interior (⋃ i, F i)) := by
    apply closure_mono
    apply interior_mono
    exact Set.subset_iUnion _ i
  exact hsubset hxi

theorem P1_closure_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P1 A) (hB : Topology.P1 B) : Topology.P1 (closure A ∪ closure B) := by
  have hA_closure : Topology.P1 (closure A) := Topology.P1_of_closure hA
  have hB_closure : Topology.P1 (closure B) := Topology.P1_of_closure hB
  simpa using Topology.P1_union hA_closure hB_closure

theorem P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P2 A := by
  intro x hx
  -- Since `A` is open, its interior is `A`
  have hx_int : x ∈ interior A := by
    simpa [hA.interior_eq] using hx
  -- `interior A` is open and contained in its closure, therefore contained
  -- in the interior of that closure
  have hsubset : (interior A : Set X) ⊆ interior (closure (interior A)) := by
    apply interior_maximal
    · intro y hy
      exact subset_closure hy
    · exact isOpen_interior
  exact hsubset hx_int

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {𝒮 : Set (Set X)} (hS : ∀ A ∈ 𝒮, Topology.P1 A) : Topology.P1 (⋃₀ 𝒮) := by
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP1A : Topology.P1 A := hS A hA_mem
  have hx_closure : x ∈ closure (interior A) := hP1A hxA
  have hsubset : (closure (interior A) : Set X) ⊆ closure (interior (⋃₀ 𝒮)) := by
    apply closure_mono
    apply interior_mono
    intro y hy
    exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
  exact hsubset hx_closure

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P3 (interior A) := by
  intro x hx
  -- `interior A` is open and contained in its closure,
  -- hence contained in the interior of that closure
  have hsubset : (interior A : Set X) ⊆ interior (closure (interior A)) := by
    apply interior_maximal
    · intro y hy
      exact subset_closure hy
    · exact isOpen_interior
  exact hsubset hx

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {𝒮 : Set (Set X)} (hS : ∀ A ∈ 𝒮, Topology.P2 A) : Topology.P2 (⋃₀ 𝒮) := by
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP2A : Topology.P2 A := hS A hA_mem
  have hx_in : x ∈ interior (closure (interior A)) := hP2A hxA
  have hsubset :
      (interior (closure (interior A)) : Set X) ⊆
        interior (closure (interior (⋃₀ 𝒮))) := by
    apply interior_mono
    apply closure_mono
    apply interior_mono
    intro y hy
    exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
  exact hsubset hx_in

theorem P3_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {F : ι → Set X} (hF : ∀ i, Topology.P3 (F i)) : Topology.P3 (⋃ i, F i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  have hxi' : x ∈ interior (closure (F i)) := hF i hxi
  have hsubset :
      (interior (closure (F i)) : Set X) ⊆ interior (closure (⋃ i, F i)) := by
    apply interior_mono
    apply closure_mono
    exact Set.subset_iUnion _ i
  exact hsubset hxi'

theorem P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 (interior A) := by
  intro x hx
  have h_int : x ∈ interior (interior A) := by
    simpa [isOpen_interior.interior_eq] using hx
  exact subset_closure h_int

theorem P3_preimage_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) {U : Set Y} (hU : IsOpen U) : Topology.P3 (f ⁻¹' U) := by
  have h_open : IsOpen (f ⁻¹' U) := hU.preimage hf
  simpa using (Topology.P3_of_open h_open)

theorem exists_dense_P1 {X : Type*} [TopologicalSpace X] : ∃ A : Set X, closure A = Set.univ ∧ Topology.P1 A := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · simp
  · simpa using Topology.P1_univ

theorem P1_iff_dense {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A ↔ closure (interior A) = closure A := by
  constructor
  · intro hP1
    apply le_antisymm
    · -- `closure (interior A)` is contained in `closure A`
      exact closure_mono (interior_subset : (interior A : Set X) ⊆ A)
    · -- use `hP1 : A ⊆ closure (interior A)` to get the reverse inclusion
      have : (A : Set X) ⊆ closure (interior A) := hP1
      simpa [closure_closure] using (closure_mono this)
  · intro hEq
    -- we must show `A ⊆ closure (interior A)`
    intro x hx
    -- `x` is in the closure of `A`
    have hx_closure : x ∈ closure A := subset_closure hx
    -- rewrite using the equality of closures
    simpa [hEq] using hx_closure

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : closure A = Set.univ) : Topology.P3 A := by
  intro x hx
  simpa [hA, isOpen_univ.interior_eq] using (Set.mem_univ x)

theorem exists_nonempty_P3 {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ A : Set X, A.Nonempty ∧ Topology.P3 A := by
  classical
  obtain ⟨x⟩ := (‹Nonempty X›)
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · exact ⟨x, by simp⟩
  · simpa using (P3_of_open (A := (Set.univ : Set X)) isOpen_univ)

theorem P2_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {F : ι → Set X} (hF : ∀ i, Topology.P2 (F i)) : Topology.P2 (⋃ i, F i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxFi⟩
  have hx_in : x ∈ interior (closure (interior (F i))) := (hF i) hxFi
  have hsubset :
      (interior (closure (interior (F i))) : Set X) ⊆
        interior (closure (interior (⋃ i, F i))) := by
    apply interior_mono
    apply closure_mono
    apply interior_mono
    exact Set.subset_iUnion _ i
  exact hsubset hx_in

theorem P2_iff_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P2 A ↔ Topology.P3 A := by
  constructor
  · intro hP2
    exact P2_implies_P3 hP2
  · intro _hP3
    exact P2_of_open hA

theorem P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hA : closure (interior A) = Set.univ) : Topology.P1 A := by
  intro x hx
  simpa [hA] using (Set.mem_univ x)

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {𝒮 : Set (Set X)} (hS : ∀ A ∈ 𝒮, Topology.P3 A) : Topology.P3 (⋃₀ 𝒮) := by
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP3A : Topology.P3 A := hS A hA_mem
  have hx_in : x ∈ interior (closure A) := hP3A hxA
  have hsubset :
      (interior (closure A) : Set X) ⊆ interior (closure (⋃₀ 𝒮)) := by
    apply interior_mono
    apply closure_mono
    intro y hy
    exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
  exact hsubset hx_in

theorem P2_preimage_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) {U : Set Y} (hU : IsOpen U) : Topology.P2 (f ⁻¹' U) := by
  have h_open : IsOpen (f ⁻¹' U) := hU.preimage hf
  simpa using (Topology.P2_of_open h_open)

theorem P1_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P1 A := by
  intro x hx
  have hx_int : x ∈ interior A := by
    simpa [hA.interior_eq] using hx
  exact subset_closure hx_int

theorem P2_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P2 A) (hB : Topology.P2 B) : Topology.P2 (Set.prod A B) := by
  intro x hx
  rcases x with ⟨a, b⟩
  rcases hx with ⟨ha, hb⟩
  have ha' : a ∈ interior (closure (interior A)) := hA ha
  have hb' : b ∈ interior (closure (interior B)) := hB hb
  have : (a, b) ∈ interior (closure (interior (A ×ˢ B))) := by
    simpa [interior_prod_eq, closure_prod_eq] using And.intro ha' hb'
  exact this

theorem P3_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P3 A) (hB : Topology.P3 B) : Topology.P3 (Set.prod A B) := by
  intro x hx
  rcases x with ⟨a, b⟩
  rcases hx with ⟨ha, hb⟩
  have ha' : a ∈ interior (closure A) := hA ha
  have hb' : b ∈ interior (closure B) := hB hb
  have hmem : (a, b) ∈ interior (closure (A ×ˢ B)) := by
    -- rewrite via `closure_prod_eq` and `interior_prod_eq`
    have : (a, b) ∈ (interior (closure A) ×ˢ interior (closure B)) := by
      exact ⟨ha', hb'⟩
    simpa [closure_prod_eq, interior_prod_eq] using this
  exact hmem

theorem P1_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P1 A) (hB : Topology.P1 B) : Topology.P1 (Set.prod A B) := by
  intro x hx
  rcases x with ⟨a, b⟩
  rcases hx with ⟨ha, hb⟩
  have ha' : a ∈ closure (interior A) := hA ha
  have hb' : b ∈ closure (interior B) := hB hb
  have : (a, b) ∈ closure (interior (A ×ˢ B)) := by
    simpa [interior_prod_eq, closure_prod_eq] using And.intro ha' hb'
  exact this

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hA : closure (interior A) = Set.univ) : Topology.P2 A := by
  intro x hx
  simpa [hA, isOpen_univ.interior_eq] using (Set.mem_univ x)

theorem P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hA : closure (interior A) = Set.univ) : Topology.P3 A := by
  have hP2 : Topology.P2 A := P2_of_dense_interior (X := X) (A := A) hA
  exact P2_implies_P3 hP2

theorem P3_univ {X : Type*} [TopologicalSpace X] : Topology.P3 (Set.univ : Set X) := by
  intro x hx
  simpa [closure_univ, isOpen_univ.interior_eq] using hx

theorem P2_univ {X : Type*} [TopologicalSpace X] : Topology.P2 (Set.univ : Set X) := by
  intro x hx
  simpa [closure_univ, isOpen_univ.interior_eq] using hx

theorem P1_iff_P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P1 A ↔ Topology.P2 A := by
  constructor
  · intro _hP1
    exact P2_of_open (X := X) (A := A) hA
  · intro hP2
    exact P2_implies_P1 (X := X) (A := A) hP2

theorem P2_of_P1_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (h1 : Topology.P1 A) (h3 : Topology.P3 A) : Topology.P2 A := by
  intro x hx
  -- `P1` gives an equality of closures
  have h_eq : (closure (interior A) : Set X) = closure A :=
    (Topology.P1_iff_dense).1 h1
  -- `P3` yields membership in `interior (closure A)`
  have hx_int : x ∈ interior (closure A) := h3 hx
  -- Rewrite using the equality of closures
  simpa [h_eq] using hx_int

theorem P2_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : Topology.P2 A) : Topology.P2 (Set.prod A (Set.univ : Set Y)) := by
  simpa using
    (Topology.P2_prod
        (X := X) (Y := Y)
        (A := A) (B := (Set.univ : Set Y))
        hA
        (Topology.P2_univ (X := Y)))

theorem P1_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P1 A := by
  -- Unfold the definition of `P1`
  unfold Topology.P1
  intro x hx
  classical
  -- First, show that `A` must be the whole space `Set.univ`
  have hA_univ : (A : Set X) = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      have h_eq : y = x := Subsingleton.elim y x
      simpa [h_eq] using hx
  -- Rewriting with `A = Set.univ`, everything becomes immediate
  simpa [hA_univ, isOpen_univ.interior_eq, closure_univ] using (Set.mem_univ x)

theorem P2_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P2 A := by
  intro x hx
  classical
  -- `A` is nonempty (since `x ∈ A`) and the space is a subsingleton,
  -- hence `A = univ`.
  have hA_univ : (A : Set X) = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      have h_eq : y = x := Subsingleton.elim y x
      simpa [h_eq] using hx
  -- Rewrite the goal using `hA_univ`; it reduces to `x ∈ univ`, solved by `simp`.
  simpa [hA_univ, closure_univ, isOpen_univ.interior_eq] using (by
    simp : x ∈ (Set.univ : Set X))

theorem P3_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P3 A := by
  -- Unfold the definition of `P3`
  unfold Topology.P3
  intro x hx
  classical
  -- In a subsingleton space any nonempty set is the whole space
  have hA_univ : (A : Set X) = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      have h_eq : y = x := Subsingleton.elim y x
      simpa [h_eq] using hx
  -- Rewriting with `A = univ`, the goal becomes trivial
  simpa [hA_univ, closure_univ, isOpen_univ.interior_eq] using (Set.mem_univ x)

theorem P1_prod_self {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P1 A) : Topology.P1 (A ×ˢ A) := by
  simpa using
    (Topology.P1_prod (X := X) (Y := X) (A := A) (B := A) hA hA)

theorem exists_compact_P3 {X : Type*} [TopologicalSpace X] : ∃ K : Set X, IsCompact K ∧ Topology.P3 K := by
  exact ⟨(∅ : Set X), isCompact_empty, (P3_empty (X := X))⟩

theorem P1_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : Topology.P1 A) : Topology.P1 (Set.prod A (Set.univ : Set Y)) := by
  simpa using
    (Topology.P1_prod
        (X := X) (Y := Y)
        (A := A) (B := (Set.univ : Set Y))
        hA
        (Topology.P1_univ (X := Y)))

theorem P3_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : Topology.P3 A) : Topology.P3 (Set.prod A (Set.univ : Set Y)) := by
  simpa using
    (Topology.P3_prod
        (X := X) (Y := Y)
        (A := A) (B := (Set.univ : Set Y))
        hA
        (Topology.P3_univ (X := Y)))

theorem P2_iff_P1_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A ↔ (Topology.P1 A ∧ Topology.P3 A) := by
  constructor
  · intro hP2
    exact
      And.intro
        (Topology.P2_implies_P1 (X := X) (A := A) hP2)
        (Topology.P2_implies_P3 (X := X) (A := A) hP2)
  · rintro ⟨hP1, hP3⟩
    exact Topology.P2_of_P1_P3 (X := X) (A := A) hP1 hP3

theorem exists_countable_P1 {X : Type*} [TopologicalSpace X] : ∃ A : Set X, Set.Countable A ∧ Topology.P1 A := by
  refine ⟨(∅ : Set X), Set.countable_empty, ?_⟩
  intro x hx
  cases hx

theorem exists_countable_P2 {X : Type*} [TopologicalSpace X] : ∃ A : Set X, Set.Countable A ∧ Topology.P2 A := by
  exact ⟨(∅ : Set X), Set.countable_empty, Topology.P2_empty (X := X)⟩

theorem P2_iff_P3_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P2 A ↔ Topology.P3 A := by
  classical
  -- Useful inclusions relating `A`, its interior, and the closure of its interior
  have h_closure_subset : (closure (interior A) : Set X) ⊆ A := by
    have : (closure (interior A) : Set X) ⊆ closure A :=
      closure_mono (interior_subset : (interior A : Set X) ⊆ A)
    simpa [hA.closure_eq] using this
  have h_int_subset : (interior (closure (interior A)) : Set X) ⊆ interior A :=
    interior_mono h_closure_subset
  have h_subset_int : (interior A : Set X) ⊆ interior (closure (interior A)) := by
    apply interior_maximal
    · intro y hy
      exact subset_closure hy
    · exact isOpen_interior
  -- Prove the equivalence
  constructor
  · -- `P2 → P3`
    intro hP2
    intro x hx
    have hx₁ : x ∈ interior (closure (interior A)) := hP2 hx
    have hx₂ : x ∈ interior A := h_int_subset hx₁
    simpa [hA.closure_eq] using hx₂
  · -- `P3 → P2`
    intro hP3
    intro x hx
    have hx₁ : x ∈ interior (closure A) := hP3 hx
    have hx_intA : x ∈ interior A := by
      simpa [hA.closure_eq] using hx₁
    exact h_subset_int hx_intA

theorem P3_of_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P3 (closure A)) : Topology.P3 A := by
  intro x hx
  have hx_closure : x ∈ closure A := subset_closure hx
  have hx_int : x ∈ interior (closure (closure A)) := h hx_closure
  simpa [closure_closure] using hx_int

theorem P3_iff_P1_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = Set.univ) : Topology.P3 A ↔ Topology.P1 A := by
  -- First, obtain `P2 A` from the density assumption.
  have hP2 : Topology.P2 A :=
    Topology.P2_of_dense_interior (X := X) (A := A) h
  -- From `P2 A` we can extract both `P1 A` and `P3 A`.
  have hP1 : Topology.P1 A :=
    ((Topology.P2_iff_P1_P3 (X := X) (A := A)).1 hP2).1
  have hP3 : Topology.P3 A :=
    ((Topology.P2_iff_P1_P3 (X := X) (A := A)).1 hP2).2
  exact ⟨fun _ => hP1, fun _ => hP3⟩

theorem P3_exists_dense {X : Type*} [TopologicalSpace X] : ∃ A : Set X, Topology.P3 A ∧ Dense A := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · exact P3_univ (X := X)
  · simpa using dense_univ

theorem P1_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {A : Set X} (hA : Topology.P1 A) : Topology.P1 (e '' A) := by
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` is in the closure of the interior of `A`
  have hx_cl : (x : X) ∈ closure (interior A) := hA hxA
  -- transport the membership through the homeomorphism
  have : (e x) ∈ closure (interior (e '' A)) := by
    -- first, regard it as a point in `e '' closure (interior A)`
    have h1 : (e x) ∈ e '' closure (interior A) := by
      exact ⟨x, hx_cl, rfl⟩
    -- rewrite using `image_closure`
    have h2 : (e x) ∈ closure (e '' interior A) := by
      simpa [e.image_closure (interior A)] using h1
    -- rewrite using `image_interior`
    simpa [e.image_interior A] using h2
  exact this

theorem P2_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {A : Set X} (hA : Topology.P2 A) : Topology.P2 (e '' A) := by
  intro y hy
  -- Pick a preimage point `x`
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` lies in the interior of the closure of the interior of `A`
  have hx_int : x ∈ interior (closure (interior A)) := hA hxA
  -- Transport this membership through `e`
  have h₁ : (e x : Y) ∈ e '' interior (closure (interior A)) :=
    ⟨x, hx_int, rfl⟩
  -- Rewrite using `image_interior`
  have h₂ : (e x) ∈ interior (e '' closure (interior A)) := by
    simpa [e.image_interior (closure (interior A))] using h₁
  -- Rewrite using `image_closure`
  have h₃ : (e x) ∈ interior (closure (e '' interior A)) := by
    simpa [e.image_closure (interior A)] using h₂
  -- Relate the two closures via `image_interior`
  have h_closure_eq :
      (closure (e '' interior A) : Set Y) = closure (interior (e '' A)) := by
    simpa using
      congrArg (closure : Set Y → Set Y) (e.image_interior A)
  -- Conclude by rewriting with the obtained equality
  simpa [h_closure_eq] using h₃

theorem P3_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {A : Set X} (hA : Topology.P3 A) : Topology.P3 (e '' A) := by
  intro y hy
  -- pick a preimage point `x`
  rcases hy with ⟨x, hxA, rfl⟩
  -- from `P3` we know `x ∈ interior (closure A)`
  have hx_int : (x : X) ∈ interior (closure A) := hA hxA
  -- transport through `e`
  have h₁ : (e x : Y) ∈ e '' interior (closure A) := ⟨x, hx_int, rfl⟩
  -- rewrite using `image_interior`
  have h₂ : (e x) ∈ interior (e '' closure A) := by
    simpa [e.image_interior (closure A)] using h₁
  -- rewrite using `image_closure` and finish
  simpa [e.image_closure A] using h₂

theorem P1_iff_P1_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} : Topology.P1 A ↔ Topology.P1 (e '' A) := by
  constructor
  · intro hA
    exact P1_image_homeomorph (e := e) hA
  · intro hImg
    -- transport `P1` back through `e.symm`
    have h' : Topology.P1 ((e.symm) '' (e '' A)) :=
      P1_image_homeomorph (e := e.symm) (A := e '' A) hImg
    -- identify the image `e.symm '' (e '' A)` with `A`
    have hEq : ((e.symm) '' (e '' A) : Set X) = A := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨y, hy, rfl⟩
        rcases hy with ⟨z, hz, rfl⟩
        simpa using hz
      · intro hx
        exact ⟨e x, ⟨x, hx, rfl⟩, by
          simp⟩
    simpa [hEq] using h'

theorem P1_iff_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P1 A ↔ Topology.P3 A := by
  simpa using
    ((Topology.P1_iff_P2_of_open (X := X) (A := A) hA).trans
      (Topology.P2_iff_P3_of_open (X := X) (A := A) hA))

theorem exists_dense_P2 {X : Type*} [TopologicalSpace X] : ∃ A : Set X, Topology.P2 A ∧ Dense A := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · exact Topology.P2_univ (X := X)
  · simpa using dense_univ

theorem P1_closed_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) (hP3 : Topology.P3 A) : Topology.P1 A := by
  intro x hx
  have hx_int : x ∈ interior A := by
    have : x ∈ interior (closure A) := hP3 hx
    simpa [hA.closure_eq] using this
  exact subset_closure hx_int

theorem exists_nontrivial_P2 {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ A : Set X, A.Nonempty ∧ Topology.P2 A := by
  classical
  obtain ⟨x⟩ := ‹Nonempty X›
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · exact ⟨x, by simp⟩
  · simpa using (P2_univ (X := X))

theorem exists_dense_P1_closed {X : Type*} [TopologicalSpace X] : ∃ A : Set X, IsClosed A ∧ Dense A ∧ Topology.P1 A := by
  refine ⟨(Set.univ : Set X), isClosed_univ, dense_univ, ?_⟩
  simpa using Topology.P1_univ (X := X)

theorem P2_diff {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P2 A) (hB : IsClosed B) : Topology.P2 (A \ B) := by
  intro x hx
  -- Decompose the membership `x ∈ A \ B`
  rcases hx with ⟨hxA, hx_notB⟩
  -- From `P2 A` we get that `x` belongs to `interior (closure (interior A))`
  have hx_int : (x : X) ∈ interior (closure (interior A)) := hA hxA
  -- Introduce an auxiliary open set
  set S : Set X := interior (closure (interior A)) ∩ Bᶜ with hS_def
  -- The set `S` is open
  have hS_open : IsOpen S := by
    have h₁ : IsOpen (interior (closure (interior A))) := isOpen_interior
    have h₂ : IsOpen (Bᶜ : Set X) := hB.isOpen_compl
    simpa [hS_def] using h₁.inter h₂
  -- Show that `S ⊆ closure (interior (A \ B))`
  have hS_subset : (S : Set X) ⊆ closure (interior (A \ B)) := by
    intro y hy
    rcases hy with ⟨hy_int, hy_notB⟩
    -- `y` is in the closure of `interior A`
    have hy_closure : y ∈ closure (interior A) := interior_subset hy_int
    -- We prove `y ∈ closure (interior (A \ B))` using `mem_closure_iff`
    have : y ∈ closure (interior (A \ B)) := by
      apply (mem_closure_iff).2
      intro o ho hy_o
      -- Consider the open neighbourhood `o ∩ Bᶜ`
      have hB_open : IsOpen (Bᶜ : Set X) := hB.isOpen_compl
      have ho₁_open : IsOpen (o ∩ Bᶜ) := ho.inter hB_open
      have hy_o₁ : y ∈ o ∩ Bᶜ := ⟨hy_o, hy_notB⟩
      -- Since `y ∈ closure (interior A)`, this open set meets `interior A`
      have h_meet : ((o ∩ Bᶜ) ∩ interior A).Nonempty := by
        have h_cond := (mem_closure_iff).1 hy_closure
        have h := h_cond (o ∩ Bᶜ) ho₁_open hy_o₁
        simpa [Set.inter_assoc, Set.inter_left_comm] using h
      rcases h_meet with ⟨w, ⟨hw_o, hw_notB⟩, hw_intA⟩
      -- Show that `w ∈ interior (A \ B)`
      have hU_open : IsOpen (interior A ∩ Bᶜ) :=
        (isOpen_interior).inter hB_open
      have hU_subset : (interior A ∩ Bᶜ : Set X) ⊆ A \ B := by
        intro z hz
        rcases hz with ⟨hz_intA, hz_notB⟩
        have hzA : z ∈ A := interior_subset hz_intA
        exact ⟨hzA, hz_notB⟩
      have hU_subset_int :
          (interior A ∩ Bᶜ : Set X) ⊆ interior (A \ B) :=
        interior_maximal hU_subset hU_open
      have hw_intAB : w ∈ interior (A \ B) :=
        hU_subset_int ⟨hw_intA, hw_notB⟩
      -- Hence `o` meets `interior (A \ B)`
      exact ⟨w, hw_o, hw_intAB⟩
    simpa using this
  -- `x` belongs to `S`
  have hxS : x ∈ S := by
    have hx_comp : x ∈ (Bᶜ : Set X) := by
      simp [hx_notB]
    simpa [hS_def] using And.intro hx_int hx_comp
  -- `S` is an open neighbourhood of `x` contained in the desired closure,
  -- hence `x` is in its interior
  have hx_target :
      (x : X) ∈ interior (closure (interior (A \ B))) :=
    (interior_maximal hS_subset hS_open) hxS
  exact hx_target

theorem P3_diff {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P3 A) (hB : IsClosed B) : Topology.P3 (A \ B) := by
  intro x hx
  rcases hx with ⟨hxA, hxNotB⟩
  -- `x` lies in the interior of the closure of `A`
  have hx_int : (x : X) ∈ interior (closure A) := hA hxA
  -- Define an auxiliary open set
  set S : Set X := interior (closure A) ∩ Bᶜ with hS_def
  -- `S` is open
  have hS_open : IsOpen S := by
    have h₁ : IsOpen (interior (closure A)) := isOpen_interior
    have h₂ : IsOpen (Bᶜ : Set X) := hB.isOpen_compl
    simpa [hS_def] using h₁.inter h₂
  -- `x` belongs to `S`
  have hxS : x ∈ S := by
    have : x ∈ interior (closure A) ∧ x ∈ Bᶜ := ⟨hx_int, hxNotB⟩
    simpa [hS_def] using this
  -- Show that `S ⊆ closure (A \ B)`
  have hS_subset : (S : Set X) ⊆ closure (A \ B) := by
    intro y hyS
    -- Decompose membership in `S`
    have hyInt_and_notB : y ∈ interior (closure A) ∧ y ∈ Bᶜ := by
      simpa [hS_def] using hyS
    have hy_int  := hyInt_and_notB.1
    have hy_notB := hyInt_and_notB.2
    -- Hence `y ∈ closure A`
    have hy_clA : y ∈ closure A := interior_subset hy_int
    -- Prove `y ∈ closure (A \ B)`
    have : y ∈ closure (A \ B) := by
      -- Use `mem_closure_iff`
      apply (mem_closure_iff).2
      intro V hVopen hyV
      -- Consider the open neighbourhood `V ∩ Bᶜ`
      have hVB_open : IsOpen (V ∩ Bᶜ) := hVopen.inter hB.isOpen_compl
      have hyVBC : y ∈ V ∩ Bᶜ := ⟨hyV, hy_notB⟩
      -- Since `y ∈ closure A`, this set meets `A`
      have h_nonempty : ((V ∩ Bᶜ) ∩ A).Nonempty := by
        have := (mem_closure_iff).1 hy_clA (V ∩ Bᶜ) hVB_open hyVBC
        simpa [Set.inter_assoc, Set.inter_left_comm] using this
      rcases h_nonempty with ⟨z, hz⟩
      rcases hz with ⟨⟨hzV, hzNotB⟩, hzA⟩
      have hz_in_diff : z ∈ A \ B := ⟨hzA, hzNotB⟩
      exact ⟨z, hzV, hz_in_diff⟩
    exact this
  -- Apply `interior_maximal` to obtain the desired inclusion
  have hS_int : (S : Set X) ⊆ interior (closure (A \ B)) :=
    interior_maximal hS_subset hS_open
  -- Conclude for the original point `x`
  exact hS_int hxS

theorem exists_closed_P2 {X : Type*} [TopologicalSpace X] : ∃ A : Set X, IsClosed A ∧ Topology.P2 A := by
  exact ⟨(∅ : Set X), isClosed_empty, Topology.P2_empty (X := X)⟩

theorem exists_dense_P3_closed {X : Type*} [TopologicalSpace X] : ∃ A : Set X, IsClosed A ∧ Dense A ∧ Topology.P3 A := by
  refine ⟨(Set.univ : Set X), isClosed_univ, dense_univ, ?_⟩
  simpa using Topology.P3_univ (X := X)

theorem P1_subset_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A → closure (interior A) ⊆ closure A := by
  intro _hP1
  exact closure_mono (interior_subset : (interior A : Set X) ⊆ A)

theorem P1_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : Topology.P1 A) (hB : Topology.P1 B) (hC : Topology.P1 C) : Topology.P1 (Set.prod (Set.prod A B) C) := by
  -- First, use `hA` and `hB` to obtain `P1` for the product `A ×ˢ B`.
  have hAB : Topology.P1 (Set.prod A B) :=
    Topology.P1_prod (X := X) (Y := Y) (A := A) (B := B) hA hB
  -- Combine `hAB` with `hC` to get the desired result.
  simpa using
    (Topology.P1_prod
        (X := X × Y) (Y := Z)
        (A := Set.prod A B) (B := C)
        hAB hC)

theorem P2_iff_exists_open_subset {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A ↔ ∀ x ∈ A, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ interior (closure (interior A)) := by
  constructor
  · intro hP2 x hx
    refine ⟨interior (closure (interior A)), isOpen_interior, ?_, ?_⟩
    · exact hP2 hx
    · intro y hy
      exact hy
  · intro h
    intro x hx
    rcases h x hx with ⟨U, _hUopen, hxU, hUsubset⟩
    exact hUsubset hxU

theorem exists_nonempty_closed_P1 {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ A : Set X, A.Nonempty ∧ IsClosed A ∧ Topology.P1 A := by
  refine ⟨(Set.univ : Set X), ?_, isClosed_univ, ?_⟩
  ·
    rcases ‹Nonempty X› with ⟨x⟩
    exact ⟨x, by simp⟩
  ·
    simpa using Topology.P1_univ (X := X)

theorem P1_inter_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 (closure (interior A) ∩ A) := by
  -- Let `x` be a point of the set `closure (interior A) ∩ A`.
  intro x hx
  -- From the membership we know `x ∈ closure (interior A)`.
  have hx_cl : x ∈ (closure (interior A) : Set X) := hx.1
  -- We show that `interior A ⊆ interior (closure (interior A) ∩ A)`.
  have h_int_subset :
      (interior A : Set X) ⊆ interior (closure (interior A) ∩ A) := by
    -- `interior A` is open …
    have h_open : IsOpen (interior A) := isOpen_interior
    -- … and contained in `closure (interior A) ∩ A`.
    have h_subset : (interior A : Set X) ⊆ closure (interior A) ∩ A := by
      intro y hy
      have hy_cl : y ∈ (closure (interior A) : Set X) := subset_closure hy
      have hy_A : y ∈ (A : Set X) :=
        (interior_subset : (interior A : Set X) ⊆ A) hy
      exact And.intro hy_cl hy_A
    -- By maximality of the interior, the claim follows.
    exact interior_maximal h_subset h_open
  -- Taking closures gives the desired inclusion of closures of interiors.
  have h_closure_subset :
      (closure (interior A) : Set X) ⊆
        closure (interior (closure (interior A) ∩ A)) :=
    closure_mono h_int_subset
  -- Apply this inclusion to `x`.
  exact h_closure_subset hx_cl

theorem P2_inter {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P2 A) (hB : Topology.P2 B) : Topology.P2 (A ∩ B) := by
  classical
  intro x hx
  rcases hx with ⟨hxA, hxB⟩
  -- `P2` for the two factors
  have hxA_int : (x : X) ∈ interior (closure (interior A)) := hA hxA
  have hxB_int : (x : X) ∈ interior (closure (interior B)) := hB hxB

  -- An auxiliary open neighbourhood of `x`
  set U : Set X :=
      interior (closure (interior A)) ∩ interior (closure (interior B)) with hU_def
  have hU_open : IsOpen U := isOpen_interior.inter isOpen_interior
  have hxU : (x : X) ∈ U := by
    have : (x : X) ∈ interior (closure (interior A)) ∧
          x ∈ interior (closure (interior B)) := ⟨hxA_int, hxB_int⟩
    simpa [hU_def] using this

  ----------------------------------------------------------------
  --  Claim:  `U ⊆ closure (interior (A ∩ B))`
  ----------------------------------------------------------------
  have hU_subset : (U : Set X) ⊆ closure (interior (A ∩ B)) := by
    intro y hyU
    -- Split the membership information carried by `hyU`
    have hyA_int : y ∈ interior (closure (interior A)) := by
      have : y ∈ interior (closure (interior A)) ∧
            y ∈ interior (closure (interior B)) := by
        simpa [hU_def] using hyU
      exact this.1
    have hyB_int : y ∈ interior (closure (interior B)) := by
      have : y ∈ interior (closure (interior A)) ∧
            y ∈ interior (closure (interior B)) := by
        simpa [hU_def] using hyU
      exact this.2
    -- Turn the two facts into membership in the two closures
    have hy_clA : y ∈ closure (interior A) := interior_subset hyA_int
    have hy_clB : y ∈ closure (interior B) := interior_subset hyB_int

    -- Show `y ∈ closure (interior (A ∩ B))` using `mem_closure_iff`
    have : (y : X) ∈ closure (interior (A ∩ B)) := by
      -- Reformulate the goal: every open nbhd of `y` meets `interior (A ∩ B)`
      apply (mem_closure_iff).2
      intro V hV_open hyV
      ----------------------------------------------------------------
      -- 1st step: shrink the neighbourhood so that it lives inside both closures
      ----------------------------------------------------------------
      set W : Set X :=
          V ∩ interior (closure (interior A)) ∩
            interior (closure (interior B)) with hW_def
      have hW_open : IsOpen W := by
        have h₁ : IsOpen (V ∩ interior (closure (interior A))) :=
          hV_open.inter isOpen_interior
        simpa [hW_def, Set.inter_assoc] using h₁.inter isOpen_interior
      have hyW : y ∈ W := by
        have : y ∈ V ∧ y ∈ interior (closure (interior A)) ∧
                y ∈ interior (closure (interior B)) := ⟨hyV, hyA_int, hyB_int⟩
        simpa [hW_def, Set.inter_assoc] using this

      ----------------------------------------------------------------
      -- 2nd step: `W` meets `interior A`
      ----------------------------------------------------------------
      have hWA_nonempty : (W ∩ interior A).Nonempty := by
        -- `y ∈ closure (interior A)` so every neighbourhood meets it
        have := (mem_closure_iff).1 hy_clA W hW_open hyW
        simpa [Set.inter_left_comm, Set.inter_assoc] using this
      rcases hWA_nonempty with ⟨z₁, hz₁W, hz₁_intA⟩

      ----------------------------------------------------------------
      -- 3rd step: shrink once more around `z₁`
      ----------------------------------------------------------------
      set W₁ : Set X :=
          V ∩ interior (closure (interior B)) ∩ interior A with hW₁_def
      have hW₁_open : IsOpen W₁ := by
        have h₁ : IsOpen (V ∩ interior (closure (interior B))) :=
          hV_open.inter isOpen_interior
        simpa [hW₁_def, Set.inter_left_comm, Set.inter_assoc] using
          h₁.inter isOpen_interior

      -- show that `z₁ ∈ W₁`
      have hz₁V : (z₁ : X) ∈ V := by
        -- unpack `hz₁W`
        have : z₁ ∈ V ∧ z₁ ∈ interior (closure (interior A)) ∧
                z₁ ∈ interior (closure (interior B)) := by
          have : z₁ ∈ W := hz₁W
          simpa [hW_def, Set.inter_assoc] using this
        exact this.1
      have hz₁Bcl_int : z₁ ∈ interior (closure (interior B)) := by
        have : z₁ ∈ V ∧ z₁ ∈ interior (closure (interior A)) ∧
                z₁ ∈ interior (closure (interior B)) := by
          have : z₁ ∈ W := hz₁W
          simpa [hW_def, Set.inter_assoc] using this
        exact this.2.2
      have hz₁W₁ : z₁ ∈ W₁ := by
        have h : z₁ ∈ V ∧ z₁ ∈ interior (closure (interior B)) ∧
                 z₁ ∈ interior A :=
          And.intro hz₁V (And.intro hz₁Bcl_int hz₁_intA)
        simpa [hW₁_def, Set.inter_left_comm, Set.inter_assoc] using h

      ----------------------------------------------------------------
      -- 4th step: `W₁` meets `interior B`
      ----------------------------------------------------------------
      have hz₁_clB : z₁ ∈ closure (interior B) := by
        have : z₁ ∈ interior (closure (interior B)) := hz₁Bcl_int
        exact interior_subset this
      have hW₁_nonempty : (W₁ ∩ interior B).Nonempty :=
        (mem_closure_iff).1 hz₁_clB W₁ hW₁_open hz₁W₁
      rcases hW₁_nonempty with ⟨z, hzW₁, hz_intB⟩

      ----------------------------------------------------------------
      -- 5th step: properties of `z`
      ----------------------------------------------------------------
      have hz_components :
          z ∈ V ∧ z ∈ interior (closure (interior B)) ∧
            z ∈ interior A := by
        simpa [hW₁_def, Set.inter_left_comm, Set.inter_assoc] using hzW₁
      have hz_in_V : z ∈ V := hz_components.1
      have hz_intA : z ∈ interior A := hz_components.2.2

      -- `z ∈ interior A ∩ interior B`
      have hz_intAB : z ∈ interior (A ∩ B) := by
        -- `interior A ∩ interior B` is open and contained in `A ∩ B`
        have h_subset :
            (interior A ∩ interior B : Set X) ⊆ A ∩ B := by
          intro w hw
          exact
            ⟨(interior_subset : (interior A : Set X) ⊆ A) hw.1,
             (interior_subset : (interior B : Set X) ⊆ B) hw.2⟩
        have h_open : IsOpen (interior A ∩ interior B) :=
          isOpen_interior.inter isOpen_interior
        have hz_mem : z ∈ interior A ∩ interior B := ⟨hz_intA, hz_intB⟩
        exact (interior_maximal h_subset h_open) hz_mem

      -- Thus `V` meets `interior (A ∩ B)` at the point `z`
      exact ⟨z, hz_in_V, hz_intAB⟩
    exact this

  ----------------------------------------------------------------
  --  Finish:  `x` is in the interior of that closure.
  ----------------------------------------------------------------
  have hx_goal : (x : X) ∈ interior (closure (interior (A ∩ B))) :=
    (interior_maximal hU_subset hU_open) hxU
  exact hx_goal

theorem exists_dense_closed_P2 {X : Type*} [TopologicalSpace X] : ∃ A : Set X, IsClosed A ∧ Dense A ∧ Topology.P2 A := by
  refine ⟨(Set.univ : Set X), isClosed_univ, dense_univ, ?_⟩
  simpa using (Topology.P2_univ (X := X))

theorem P1_iff_closure_interior_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P1 A ↔ closure (interior A) = A := by
  simpa [hA.closure_eq] using (Topology.P1_iff_dense (X := X) (A := A))

theorem P3_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : Topology.P3 A) (hB : Topology.P3 B) (hC : Topology.P3 C) : Topology.P3 (Set.prod (Set.prod A B) C) := by
  -- Obtain `P3` for the product `A ×ˢ B`
  have hAB : Topology.P3 (Set.prod A B) :=
    Topology.P3_prod (X := X) (Y := Y) (A := A) (B := B) hA hB
  -- Combine with `hC` to get the desired result
  simpa using
    (Topology.P3_prod
        (X := X × Y) (Y := Z)
        (A := Set.prod A B) (B := C)
        hAB hC)

theorem P2_compl_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) (hP2 : Topology.P2 A) : Topology.P2 (Aᶜ) := by
  simpa using (Topology.P2_of_open (X := X) (A := Aᶜ) hA.isOpen_compl)

theorem exists_open_dense_P2 {X : Type*} [TopologicalSpace X] : ∃ U : Set X, IsOpen U ∧ Dense U ∧ Topology.P2 U := by
  exact ⟨(Set.univ : Set X), isOpen_univ, dense_univ, Topology.P2_univ (X := X)⟩

theorem exists_infinite_P1 {X : Type*} [TopologicalSpace X] [Infinite X] : ∃ A : Set X, A.Infinite ∧ Topology.P1 A := by
  exact ⟨(Set.univ : Set X), Set.infinite_univ, Topology.P1_univ (X := X)⟩

theorem P3_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen (closure A)) : Topology.P3 A := by
    intro x hx
    have hx_cl : (x : X) ∈ closure A := subset_closure hx
    have h_int_eq : interior (closure A) = closure A := hA.interior_eq
    simpa [h_int_eq] using hx_cl

theorem P2_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} (hA : Topology.P2 A) (hB : Topology.P2 B) (hC : Topology.P2 C) : Topology.P2 (A ∪ B ∪ C) := by
  -- First, obtain `P2` for `A ∪ B`.
  have hAB : Topology.P2 (A ∪ B) :=
    Topology.P2_union (X := X) (A := A) (B := B) hA hB
  -- Combine with `C`.
  simpa using
    (Topology.P2_union (X := X) (A := A ∪ B) (B := C) hAB hC)

theorem P3_closed_iff {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P3 A ↔ interior A = A := by
  -- First, record that the closure of `A` is `A` itself.
  have h_closure : closure (A : Set X) = A := hA.closure_eq
  -- Establish the desired equivalence.
  constructor
  · -- `P3 A → interior A = A`
    intro hP3
    apply le_antisymm
    · -- `interior A ⊆ A`
      exact interior_subset
    · -- `A ⊆ interior A`
      have : (A : Set X) ⊆ interior (closure A) := hP3
      simpa [h_closure] using this
  · -- `interior A = A → P3 A`
    intro hIntEq
    intro x hx
    -- From `x ∈ A` and `interior A = A` we get `x ∈ interior A`.
    have hx_int : x ∈ interior A := by
      simpa [hIntEq] using hx
    -- Rewrite `interior (closure A)` using `closure A = A`.
    simpa [h_closure] using hx_int

theorem P2_subsingleton_iff {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P2 A ↔ True := by
  constructor
  · intro _h; trivial
  · intro _; exact P2_subsingleton (X := X) (A := A)

theorem P3_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} (hA : Topology.P3 A) (hB : Topology.P3 B) (hC : Topology.P3 C) : Topology.P3 (A ∪ B ∪ C) := by
  -- Obtain `P3` for `A ∪ B`
  have hAB : Topology.P3 (A ∪ B) :=
    Topology.P3_union (X := X) (A := A) (B := B) hA hB
  -- Combine with `C`
  simpa [Set.union_assoc] using
    (Topology.P3_union (X := X) (A := A ∪ B) (B := C) hAB hC)

theorem exists_open_P3 {X : Type*} [TopologicalSpace X] : ∃ U : Set X, IsOpen U ∧ Topology.P3 U := by
  refine ⟨(Set.univ : Set X), isOpen_univ, ?_⟩
  simpa using Topology.P3_univ (X := X)

theorem exists_finite_P3 {X : Type*} [TopologicalSpace X] : ∃ A : Set X, A.Finite ∧ Topology.P3 A := by
  refine ⟨(∅ : Set X), Set.finite_empty, ?_⟩
  exact Topology.P3_empty (X := X)

theorem P2_union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X} (hA : Topology.P2 A) (hB : Topology.P2 B) (hC : Topology.P2 C) (hD : Topology.P2 D) : Topology.P2 (A ∪ B ∪ C ∪ D) := by
  -- First, obtain `P2` for the union of the first three sets.
  have hABC : Topology.P2 (A ∪ B ∪ C) :=
    Topology.P2_union_three (X := X) (A := A) (B := B) (C := C) hA hB hC
  -- Combine this with `D`.
  simpa [Set.union_assoc] using
    (Topology.P2_union (X := X) (A := A ∪ B ∪ C) (B := D) hABC hD)

theorem P3_prod_four {W X Y Z : Type*} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set W} {B : Set X} {C : Set Y} {D : Set Z} (hA : Topology.P3 A) (hB : Topology.P3 B) (hC : Topology.P3 C) (hD : Topology.P3 D) : Topology.P3 (Set.prod (Set.prod (Set.prod A B) C) D) := by
  -- Obtain `P3` for the product `A ×ˢ B ×ˢ C`.
  have hABC : Topology.P3 (Set.prod (Set.prod A B) C) :=
    Topology.P3_prod_three
      (X := W) (Y := X) (Z := Y)
      (A := A) (B := B) (C := C)
      hA hB hC
  -- Combine with `D` to get the required product.
  simpa using
    (Topology.P3_prod
        (X := (W × X) × Y) (Y := Z)
        (A := Set.prod (Set.prod A B) C) (B := D)
        hABC hD)

theorem P2_of_closed_complement {X : Type*} [TopologicalSpace X] {A : Set X} (h_closed : IsClosed (Aᶜ)) : Topology.P2 A := by
  -- Since `Aᶜ` is closed, its complement `A` is open.
  have hA_open : IsOpen (A : Set X) := by
    simpa [compl_compl] using h_closed.isOpen_compl
  -- Apply the lemma that open sets satisfy `P2`.
  exact Topology.P2_of_open (X := X) (A := A) hA_open

theorem P1_prod_five {V W X Y Z : Type*} [TopologicalSpace V] [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set V} {B : Set W} {C : Set X} {D : Set Y} {E : Set Z} (hA : Topology.P1 A) (hB : Topology.P1 B) (hC : Topology.P1 C) (hD : Topology.P1 D) (hE : Topology.P1 E) : Topology.P1 (Set.prod (Set.prod (Set.prod (Set.prod A B) C) D) E) := by
  -- First, obtain `P1` for `(A ×ˢ B) ×ˢ C`.
  have hABC : Topology.P1 (Set.prod (Set.prod A B) C) :=
    Topology.P1_prod_three (A := A) (B := B) (C := C) hA hB hC
  -- Combine with `D`.
  have hABCD : Topology.P1 (Set.prod (Set.prod (Set.prod A B) C) D) :=
    Topology.P1_prod
      (A := Set.prod (Set.prod A B) C) (B := D)
      hABC hD
  -- Combine with `E` to get the desired product.
  simpa using
    (Topology.P1_prod
      (A := Set.prod (Set.prod (Set.prod A B) C) D) (B := E)
      hABCD hE)

theorem exists_nowhere_dense_P1 {X : Type*} [TopologicalSpace X] : ∃ A : Set X, closure A = A ∧ interior A = (∅ : Set X) ∧ Topology.P1 A := by
  refine ⟨(∅ : Set X), ?_, ?_, ?_⟩
  · simp
  · simp
  · intro x hx
    cases hx

theorem P3_subsingleton_iff {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P3 A ↔ True := by
  constructor
  · intro _; trivial
  · intro _; exact Topology.P3_subsingleton (X := X) (A := A)

theorem P1_union_many {X : Type*} [TopologicalSpace X] {ι : Sort*} {F : ι → Set X} (hF : ∀ i, Topology.P1 (F i)) : Topology.P1 (⋃ i, closure (F i)) := by
  -- First, upgrade each `P1 (F i)` to `P1 (closure (F i))`.
  have hG : ∀ i, Topology.P1 (closure (F i)) := fun i =>
    Topology.P1_of_closure (hF i)
  -- Apply the `P1_iUnion` lemma to the family of closures.
  simpa using
    (Topology.P1_iUnion (F := fun i => closure (F i)) hG)

theorem exists_dense_closed_nonempty_P3 {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ A : Set X, A.Nonempty ∧ Dense A ∧ IsClosed A ∧ Topology.P3 A := by
  classical
  obtain ⟨x⟩ := ‹Nonempty X›
  refine ⟨(Set.univ : Set X), ?_, dense_univ, isClosed_univ, ?_⟩
  · exact ⟨x, by simp⟩
  · simpa using Topology.P3_univ (X := X)

theorem P2_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : Topology.P2 A) (hB : Topology.P2 B) (hC : Topology.P2 C) : Topology.P2 (Set.prod (Set.prod A B) C) := by
  -- First, obtain `P2` for the product `A ×ˢ B`.
  have hAB : Topology.P2 (Set.prod A B) :=
    Topology.P2_prod (X := X) (Y := Y) (A := A) (B := B) hA hB
  -- Combine this with `C` to get the required triple product.
  simpa using
    (Topology.P2_prod
        (X := X × Y) (Y := Z)
        (A := Set.prod A B) (B := C)
        hAB hC)

theorem P1_exists_finite {X : Type*} [TopologicalSpace X] : ∃ A : Set X, A.Finite ∧ Topology.P1 A := by
  refine ⟨(∅ : Set X), Set.finite_empty, ?_⟩
  intro x hx
  cases hx

theorem exists_dense_interior_P2 {X : Type*} [TopologicalSpace X] : ∃ A : Set X, closure (interior A) = Set.univ ∧ Topology.P2 A := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · simp
  · simpa using Topology.P2_univ (X := X)

theorem P2_iff_P2_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} : Topology.P2 A ↔ Topology.P2 (e '' A) := by
  constructor
  · intro hA
    exact P2_image_homeomorph (e := e) (A := A) hA
  · intro hImg
    have h' : Topology.P2 ((e.symm) '' (e '' A)) :=
      P2_image_homeomorph (e := e.symm) (A := e '' A) hImg
    have hEq : ((e.symm) '' (e '' A) : Set X) = A := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨y, hy, rfl⟩
        rcases hy with ⟨z, hz, rfl⟩
        simpa using hz
      · intro hx
        exact ⟨e x, ⟨x, hx, rfl⟩, by
          simp⟩
    simpa [hEq] using h'

theorem exists_nonempty_open_P1 {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ U : Set X, IsOpen U ∧ U.Nonempty ∧ Topology.P1 U := by
  classical
  obtain ⟨x⟩ := (‹Nonempty X›)
  refine ⟨(Set.univ : Set X), isOpen_univ, ?_, ?_⟩
  · exact ⟨x, by simp⟩
  · simpa using Topology.P1_univ (X := X)

theorem exists_nonempty_closed_P2 {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ A : Set X, IsClosed A ∧ A.Nonempty ∧ Topology.P2 A := by
  refine ⟨(Set.univ : Set X), isClosed_univ, ?_, ?_⟩
  ·
    obtain ⟨x⟩ := (‹Nonempty X›)
    exact ⟨x, by simp⟩
  ·
    simpa using Topology.P2_univ (X := X)

theorem P1_compl_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P1 (Aᶜ) := by
  simpa using
    (Topology.P1_of_open (X := X) (A := Aᶜ) hA.isOpen_compl)

theorem exists_nowhere_dense_P2 {X : Type*} [TopologicalSpace X] : ∃ A : Set X, closure A = A ∧ interior A = (∅ : Set X) ∧ Topology.P2 A := by
  refine ⟨(∅ : Set X), ?_, ?_, ?_⟩
  · simp
  · simp
  · exact Topology.P2_empty (X := X)

theorem P2_prod_five {V W X Y Z : Type*} [TopologicalSpace V] [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set V} {B : Set W} {C : Set X} {D : Set Y} {E : Set Z} (hA : Topology.P2 A) (hB : Topology.P2 B) (hC : Topology.P2 C) (hD : Topology.P2 D) (hE : Topology.P2 E) : Topology.P2 (Set.prod (Set.prod (Set.prod (Set.prod A B) C) D) E) := by
  -- First, obtain `P2` for the triple product `(A ×ˢ B) ×ˢ C`.
  have hABC : Topology.P2 (Set.prod (Set.prod A B) C) :=
    Topology.P2_prod_three (A := A) (B := B) (C := C) hA hB hC
  -- Combine with `D` to get a fourfold product.
  have hABCD : Topology.P2 (Set.prod (Set.prod (Set.prod A B) C) D) :=
    Topology.P2_prod (A := Set.prod (Set.prod A B) C) (B := D) hABC hD
  -- Finally, combine with `E` to obtain the desired fivefold product.
  simpa using
    (Topology.P2_prod
        (A := Set.prod (Set.prod (Set.prod A B) C) D) (B := E)
        hABCD hE)

theorem P2_union_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {F : ι → Set X} (hF : ∀ i, Topology.P2 (F i)) : Topology.P2 (⋃ i, F i) := by
  simpa using (Topology.P2_iUnion (X := X) (F := F) hF)

theorem exists_open_dense_P1 {X : Type*} [TopologicalSpace X] : ∃ U : Set X, IsOpen U ∧ Dense U ∧ Topology.P1 U := by
  refine ⟨(Set.univ : Set X), isOpen_univ, dense_univ, ?_⟩
  simpa using Topology.P1_univ (X := X)

theorem P3_iff_P2_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense (interior A)) : Topology.P3 A ↔ Topology.P2 A := by
  -- From the density of `interior A` we obtain the equality of closures.
  have h_closure : (closure (interior (A : Set X)) : Set X) = Set.univ := by
    simpa using h.closure_eq
  -- This equality implies `P2 A`.
  have hP2_dense : Topology.P2 A :=
    Topology.P2_of_dense_interior (X := X) (A := A) h_closure
  -- Establish the equivalence.
  exact
    ⟨fun _hP3 => hP2_dense,
     fun hP2 => Topology.P2_implies_P3 (X := X) (A := A) hP2⟩

theorem exists_dense_P1_open_closed {X : Type*} [TopologicalSpace X] : ∃ A : Set X, IsOpen A ∧ IsClosed A ∧ Dense A ∧ Topology.P1 A := by
  refine ⟨(Set.univ : Set X), isOpen_univ, isClosed_univ, dense_univ, ?_⟩
  simpa using Topology.P1_univ (X := X)

theorem P2_prod_infinite {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Infinite X] [Infinite Y] {A : Set X} {B : Set Y} (hA : Topology.P2 A) (hB : Topology.P2 B) : Topology.P2 (A ×ˢ B) := by
  simpa using
    (Topology.P2_prod
        (X := X) (Y := Y)
        (A := A) (B := B)
        hA hB)

theorem exists_dense_P1_measurable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] : ∃ A : Set X, MeasurableSet A ∧ Dense A ∧ Topology.P1 A := by
  refine ⟨(Set.univ : Set X), ?_, ?_, ?_⟩
  · simpa using MeasurableSet.univ
  · simpa using dense_univ
  · simpa using Topology.P1_univ (X := X)

theorem exists_open_dense_P3 {X : Type*} [TopologicalSpace X] : ∃ U : Set X, IsOpen U ∧ Dense U ∧ Topology.P3 U := by
  refine ⟨(Set.univ : Set X), isOpen_univ, dense_univ, ?_⟩
  simpa using (Topology.P3_univ (X := X))

theorem P1_union_sUnion {X : Type*} [TopologicalSpace X] {𝒮 : Set (Set X)} {B : Set X} (hB : Topology.P1 B) (hS : ∀ A ∈ 𝒮, Topology.P1 A) : Topology.P1 (B ∪ ⋃₀ 𝒮) := by
  -- First obtain `P1` for the sUnion.
  have hSUnion : Topology.P1 (⋃₀ 𝒮) :=
    Topology.P1_sUnion (X := X) (𝒮 := 𝒮) hS
  -- Combine with `hB` using `P1_union`.
  simpa using
    (Topology.P1_union (A := B) (B := ⋃₀ 𝒮) hB hSUnion)

theorem P3_inter_open {X : Type*} [TopologicalSpace X] {A U : Set X} (hA : Topology.P3 A) (hU : IsOpen U) : Topology.P3 (A ∩ U) := by
  -- Unfold `P3` goal
  intro x hx
  -- `x` is in `A` and in the open set `U`
  have hxA : (x : X) ∈ A := hx.1
  have hxU : x ∈ U := hx.2
  -- From `P3 A` we get that `x ∈ interior (closure A)`
  have hxInt : (x : X) ∈ interior (closure A) := hA hxA
  --------------------------------------------------------------------
  --  Define an auxiliary open neighbourhood of `x`
  --------------------------------------------------------------------
  set S : Set X := interior (closure A) ∩ U with hS_def
  have hS_open : IsOpen S := isOpen_interior.inter hU
  have hxS : (x : X) ∈ S := by
    have : x ∈ interior (closure A) ∧ x ∈ U := ⟨hxInt, hxU⟩
    simpa [hS_def] using this
  --------------------------------------------------------------------
  --  Show that `S ⊆ closure (A ∩ U)`
  --------------------------------------------------------------------
  have hS_subset : (S : Set X) ⊆ closure (A ∩ U) := by
    intro y hyS
    have hyInt : y ∈ interior (closure A) := (by
      have h : y ∈ interior (closure A) ∧ y ∈ U := by
        simpa [hS_def] using hyS
      exact h.1)
    have hyU   : y ∈ U := (by
      have h : y ∈ interior (closure A) ∧ y ∈ U := by
        simpa [hS_def] using hyS
      exact h.2)
    -- We prove `y ∈ closure (A ∩ U)` via `mem_closure_iff`
    have : (y : X) ∈ closure (A ∩ U) := by
      apply (mem_closure_iff).2
      intro V hVopen hyV
      -- Consider the open set `V ∩ U`
      have hVU_open : IsOpen (V ∩ U) := hVopen.inter hU
      have hyVU : y ∈ V ∩ U := ⟨hyV, hyU⟩
      -- Since `y ∈ interior (closure A)`, hence `y ∈ closure A`
      have hy_clA : y ∈ closure A := interior_subset hyInt
      -- Thus `V ∩ U` meets `A`
      have h_nonempty : ((V ∩ U) ∩ A).Nonempty :=
        (mem_closure_iff).1 hy_clA (V ∩ U) hVU_open hyVU
      rcases h_nonempty with ⟨z, hzVU, hzA⟩
      -- Extract the components of `hzVU`
      have hzV : z ∈ V := hzVU.1
      have hzU : z ∈ U := hzVU.2
      -- Provide the witness that `V` meets `A ∩ U`
      exact ⟨z, hzV, ⟨hzA, hzU⟩⟩
    exact this
  --------------------------------------------------------------------
  --  `S` is an open neighbourhood of `x` contained in `closure (A ∩ U)`
  --  hence contained in its interior; conclude for `x`.
  --------------------------------------------------------------------
  have hS_int : (S : Set X) ⊆ interior (closure (A ∩ U)) :=
    interior_maximal hS_subset hS_open
  exact hS_int hxS

theorem exists_dense_P3_measurable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] : ∃ A : Set X, MeasurableSet A ∧ Topology.P3 A ∧ Dense A := by
  refine ⟨(Set.univ : Set X), ?_, ?_, ?_⟩
  · simpa using MeasurableSet.univ
  · simpa using Topology.P3_univ (X := X)
  · simpa using dense_univ

theorem P2_inter_three {X : Type*} [TopologicalSpace X] {A B C : Set X} (hA : Topology.P2 A) (hB : Topology.P2 B) (hC : Topology.P2 C) : Topology.P2 (A ∩ B ∩ C) := by
  have hAB : Topology.P2 (A ∩ B) := Topology.P2_inter (X := X) hA hB
  simpa using (Topology.P2_inter (X := X) hAB hC)

theorem exists_clopen_P1 {X : Type*} [TopologicalSpace X] : ∃ A : Set X, IsOpen A ∧ IsClosed A ∧ Topology.P1 A := by
  refine ⟨(Set.univ : Set X), isOpen_univ, isClosed_univ, ?_⟩
  simpa using Topology.P1_univ (X := X)

theorem P3_iff_P3_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} : Topology.P3 A ↔ Topology.P3 (e '' A) := by
  constructor
  · intro hA
    exact P3_image_homeomorph (e := e) (A := A) hA
  · intro hImg
    have h' : Topology.P3 ((e.symm) '' (e '' A)) :=
      P3_image_homeomorph (e := e.symm) (A := e '' A) hImg
    have hEq : ((e.symm) '' (e '' A) : Set X) = A := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨y, hy, rfl⟩
        rcases hy with ⟨z, hz, rfl⟩
        simpa using hz
      · intro hx
        exact ⟨e x, ⟨x, hx, rfl⟩, by
          simp⟩
    simpa [hEq] using h'

theorem P2_prod_four {W X Y Z : Type*} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set W} {B : Set X} {C : Set Y} {D : Set Z} (hA : Topology.P2 A) (hB : Topology.P2 B) (hC : Topology.P2 C) (hD : Topology.P2 D) : Topology.P2 (Set.prod (Set.prod (Set.prod A B) C) D) := by
  -- First, obtain `P2` for the triple product `(A ×ˢ B) ×ˢ C`.
  have hABC : Topology.P2 (Set.prod (Set.prod A B) C) :=
    Topology.P2_prod_three
      (A := A) (B := B) (C := C)
      hA hB hC
  -- Combine this with `D` to obtain the required fourfold product.
  simpa using
    (Topology.P2_prod
        (X := (W × X) × Y) (Y := Z)
        (A := Set.prod (Set.prod A B) C) (B := D)
        hABC hD)

theorem exists_measurable_P2 {X : Type*} [TopologicalSpace X] [MeasurableSpace X] : ∃ A : Set X, MeasurableSet A ∧ Topology.P2 A := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · simpa using MeasurableSet.univ
  · simpa using Topology.P2_univ (X := X)

theorem exists_measurable_P1 {X : Type*} [TopologicalSpace X] [MeasurableSpace X] : ∃ A : Set X, MeasurableSet A ∧ Topology.P1 A := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · simpa using MeasurableSet.univ
  · simpa using Topology.P1_univ (X := X)

theorem exists_measurable_P3 {X : Type*} [TopologicalSpace X] [MeasurableSpace X] : ∃ A : Set X, MeasurableSet A ∧ Topology.P3 A := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · simpa using MeasurableSet.univ
  · simpa using Topology.P3_univ (X := X)

theorem exists_dense_open_closed_P3 {X : Type*} [TopologicalSpace X] : ∃ A : Set X, IsOpen A ∧ IsClosed A ∧ Dense A ∧ Topology.P3 A := by
  refine ⟨(Set.univ : Set X), isOpen_univ, isClosed_univ, dense_univ, ?_⟩
  simpa using Topology.P3_univ (X := X)

theorem P3_prod_five {U V W X Y : Type*} [TopologicalSpace U] [TopologicalSpace V] [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] {A : Set U} {B : Set V} {C : Set W} {D : Set X} {E : Set Y} (hA : Topology.P3 A) (hB : Topology.P3 B) (hC : Topology.P3 C) (hD : Topology.P3 D) (hE : Topology.P3 E) : Topology.P3 (Set.prod (Set.prod (Set.prod (Set.prod A B) C) D) E) := by
  -- First, obtain `P3` for the fourfold product `(((A ×ˢ B) ×ˢ C) ×ˢ D)`.
  have hABCD : Topology.P3 (Set.prod (Set.prod (Set.prod A B) C) D) :=
    Topology.P3_prod_four
      (A := A) (B := B) (C := C) (D := D)
      hA hB hC hD
  -- Combine this with `E` to get the required fivefold product.
  simpa using
    (Topology.P3_prod
        (A := Set.prod (Set.prod (Set.prod A B) C) D)
        (B := E)
        hABCD hE)