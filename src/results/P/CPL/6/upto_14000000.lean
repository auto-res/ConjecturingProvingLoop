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


theorem P2_implies_P1 {A : Set X} : P2 A → P1 A := by
  intro hP2
  intro x hxA
  have hx' : x ∈ interior (closure (interior A)) := hP2 hxA
  exact interior_subset hx'

theorem P2_implies_P3 {A : Set X} : P2 A → P3 A := by
  intro hP2
  intro x hxA
  have hx1 : x ∈ interior (closure (interior A)) := hP2 hxA
  have hsubset : closure (interior A) ⊆ closure A := closure_mono interior_subset
  exact (interior_mono hsubset) hx1

theorem P3_of_dense {A : Set X} (hA : closure A = Set.univ) : P3 A := by
  intro x hx
  simpa [hA, interior_univ]

theorem P3_of_open {A : Set X} (hA : IsOpen A) : P3 A := by
  intro x hx
  have h_mem_nhds : (closure A : Set X) ∈ 𝓝 x := by
    have hA_nhds : (A : Set X) ∈ 𝓝 x := hA.mem_nhds hx
    exact
      Filter.mem_of_superset hA_nhds
        (subset_closure : (A : Set X) ⊆ closure A)
  exact (mem_interior_iff_mem_nhds).2 h_mem_nhds

theorem P2_union {A B : Set X} : P2 A → P2 B → P2 (A ∪ B) := by
  intro hP2A hP2B
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x ∈ A`
      have hx1 : x ∈ interior (closure (interior A)) := hP2A hxA
      -- `closure (interior A)` is contained in `closure (interior (A ∪ B))`
      have hsubset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inl hy
      exact (interior_mono hsubset) hx1
  | inr hxB =>
      -- `x ∈ B`
      have hx1 : x ∈ interior (closure (interior B)) := hP2B hxB
      -- `closure (interior B)` is contained in `closure (interior (A ∪ B))`
      have hsubset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inr hy
      exact (interior_mono hsubset) hx1

theorem P1_empty : P1 (∅ : Set X) := by
  intro x hx
  exact False.elim hx

theorem P2_empty : P2 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P3_univ : P3 (Set.univ : Set X) := by
  intro x hx
  simpa [closure_univ, interior_univ] using hx

theorem P1_of_open {A : Set X} (hA : IsOpen A) : P1 A := by
  intro x hx
  have : x ∈ closure A := subset_closure hx
  simpa [hA.interior_eq] using this

theorem P1_union {A B : Set X} : P1 A → P1 B → P1 (A ∪ B) := by
  intro hP1A hP1B
  intro x hx
  cases hx with
  | inl hxA =>
      have hx' : x ∈ closure (interior A) := hP1A hxA
      have hsubset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inl hy
      exact hsubset hx'
  | inr hxB =>
      have hx' : x ∈ closure (interior B) := hP1B hxB
      have hsubset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inr hy
      exact hsubset hx'

theorem closure_eq_closure_interior_of_P2 {A : Set X} (h : P2 A) : closure A = closure (interior A) := by
  apply le_antisymm
  ·
    have hA : (A : Set X) ⊆ closure (interior A) := by
      intro x hxA
      have hx' : x ∈ interior (closure (interior A)) := h hxA
      exact interior_subset hx'
    have hclosure : closure A ⊆ closure (closure (interior A)) := closure_mono hA
    simpa [closure_closure] using hclosure
  ·
    exact closure_mono interior_subset

theorem P2_of_open {A : Set X} (hA : IsOpen A) : P2 A := by
  intro x hxA
  have h_mem_nhds : (closure A : Set X) ∈ 𝓝 x := by
    have hA_nhds : (A : Set X) ∈ 𝓝 x := hA.mem_nhds hxA
    exact Filter.mem_of_superset hA_nhds (subset_closure : (A : Set X) ⊆ closure A)
  have hx_int : x ∈ interior (closure A) := (mem_interior_iff_mem_nhds).2 h_mem_nhds
  simpa [hA.interior_eq] using hx_int

theorem P3_iUnion {ι : Sort*} {A : ι → Set X} (h : ∀ i, P3 (A i)) : P3 (⋃ i, A i) := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxAi⟩
  have hx1 : x ∈ interior (closure (A i)) := (h i) hxAi
  have hsubset : closure (A i) ⊆ closure (⋃ j, A j) := by
    apply closure_mono
    intro y hy
    exact Set.mem_iUnion_of_mem i hy
  exact (interior_mono hsubset) hx1

theorem Topology.P1_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} : (∀ i, Topology.P1 (A i)) → Topology.P1 (⋃ i, A i) := by
  intro hP1
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxAi⟩
  have hx1 : x ∈ closure (interior (A i)) := (hP1 i) hxAi
  have hsubset_interior : interior (A i) ⊆ interior (⋃ j, A j) := by
    apply interior_mono
    intro y hy
    exact Set.mem_iUnion_of_mem i hy
  have hsubset : closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) :=
    closure_mono hsubset_interior
  exact hsubset hx1

theorem Topology.P2_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} : (∀ i, Topology.P2 (A i)) → Topology.P2 (⋃ i, A i) := by
  intro hP2
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxAi⟩
  have hx1 : x ∈ interior (closure (interior (A i))) := (hP2 i) hxAi
  have hsubset_interior : interior (A i) ⊆ interior (⋃ j, A j) := by
    apply interior_mono
    intro y hy
    exact Set.mem_iUnion_of_mem i hy
  have hsubset : closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) :=
    closure_mono hsubset_interior
  exact (interior_mono hsubset) hx1

theorem Topology.P1_sUnion {X : Type*} [TopologicalSpace X] {𝓢 : Set (Set X)} : (∀ A ∈ 𝓢, Topology.P1 A) → Topology.P1 (⋃₀ 𝓢) := by
  intro hP1
  intro x hx
  rcases Set.mem_sUnion.mp hx with ⟨A, hAS, hxA⟩
  have hx1 : x ∈ closure (interior A) := (hP1 A hAS) hxA
  have hA_subset : (A : Set X) ⊆ ⋃₀ 𝓢 := by
    intro y hy
    exact Set.mem_sUnion.mpr ⟨A, hAS, hy⟩
  have hsubset_interior : interior A ⊆ interior (⋃₀ 𝓢) :=
    interior_mono hA_subset
  have hsubset : closure (interior A) ⊆ closure (interior (⋃₀ 𝓢)) :=
    closure_mono hsubset_interior
  exact hsubset hx1

theorem P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P2 (interior A) := by
  intro x hx
  -- `x` is in the interior of `A`, hence every neighbourhood of `x` meets `interior A`
  have h_int_nhds : (interior A : Set X) ∈ 𝓝 x :=
    isOpen_interior.mem_nhds hx
  -- Since `interior A ⊆ closure (interior A)`, the latter is also in the neighbourhood filter
  have h_cl_nhds : (closure (interior A) : Set X) ∈ 𝓝 x :=
    Filter.mem_of_superset h_int_nhds
      (subset_closure : (interior A : Set X) ⊆ closure (interior A))
  -- Re-express the set using `interior_interior` so that types match the goal
  have h_cl_nhds' : (closure (interior (interior A)) : Set X) ∈ 𝓝 x := by
    simpa [interior_interior] using h_cl_nhds
  -- Conclude that `x` belongs to the required interior
  exact (mem_interior_iff_mem_nhds).2 h_cl_nhds'

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} : Topology.P3 A → Topology.P3 B → Topology.P3 (A ∪ B) := by
  intro hP3A hP3B
  intro x hx
  cases hx with
  | inl hxA =>
      have hx1 : x ∈ interior (closure A) := hP3A hxA
      have hsubset : closure A ⊆ closure (A ∪ B) := by
        apply closure_mono
        intro y hy
        exact Or.inl hy
      exact (interior_mono hsubset) hx1
  | inr hxB =>
      have hx1 : x ∈ interior (closure B) := hP3B hxB
      have hsubset : closure B ⊆ closure (A ∪ B) := by
        apply closure_mono
        intro y hy
        exact Or.inr hy
      exact (interior_mono hsubset) hx1

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {𝓢 : Set (Set X)} : (∀ A ∈ 𝓢, Topology.P3 A) → Topology.P3 (⋃₀ 𝓢) := by
  intro hP3
  intro x hx
  rcases Set.mem_sUnion.mp hx with ⟨A, hAS, hxA⟩
  have hx1 : x ∈ interior (closure (A : Set X)) := hP3 A hAS hxA
  have hsubset_closure : closure (A : Set X) ⊆ closure (⋃₀ (𝓢 : Set (Set X))) := by
    apply closure_mono
    intro y hy
    exact Set.mem_sUnion.mpr ⟨A, hAS, hy⟩
  have hsubset :
      interior (closure (A : Set X)) ⊆ interior (closure (⋃₀ (𝓢 : Set (Set X)))) :=
    interior_mono hsubset_closure
  exact hsubset hx1

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {𝓢 : Set (Set X)} : (∀ A ∈ 𝓢, Topology.P2 A) → Topology.P2 (⋃₀ 𝓢) := by
  intro hP2
  intro x hx
  rcases Set.mem_sUnion.mp hx with ⟨A, hAS, hxA⟩
  have hx1 : x ∈ interior (closure (interior (A : Set X))) := (hP2 A hAS) hxA
  have hA_subset : (A : Set X) ⊆ ⋃₀ 𝓢 := by
    intro y hy
    exact Set.mem_sUnion.mpr ⟨A, hAS, hy⟩
  have hsubset_interior : interior (A : Set X) ⊆ interior (⋃₀ 𝓢) :=
    interior_mono hA_subset
  have hsubset :
      closure (interior (A : Set X)) ⊆ closure (interior (⋃₀ 𝓢)) :=
    closure_mono hsubset_interior
  exact (interior_mono hsubset) hx1

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P3 (interior A) := by
  exact Topology.P2_implies_P3 (by
    simpa using (Topology.P2_interior (A := A)))

theorem Topology.P3_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P3 A → closure A = closure (interior (closure A)) := by
  intro hP3
  apply le_antisymm
  ·
    have : closure A ⊆ closure (interior (closure A)) :=
      closure_mono hP3
    simpa using this
  ·
    have : closure (interior (closure A)) ⊆ closure A := by
      have hsubset : interior (closure A) ⊆ closure A := interior_subset
      simpa [closure_closure] using closure_mono hsubset
    simpa using this

theorem Topology.P3_empty {X : Type*} [TopologicalSpace X] : Topology.P3 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P1_iff_P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P1 A ↔ P2 A := by
  constructor
  · intro _; exact P2_of_open (A := A) hA
  · intro hP2; exact P2_implies_P1 (A := A) hP2

theorem P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (interior A) := by
  simpa using (P1_of_open (A := interior A) isOpen_interior)

theorem P2_univ {X : Type*} [TopologicalSpace X] : P2 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A → Topology.P1 (closure A) := by
  intro hP1
  intro x hx_closure
  -- We will use the characterisation of closure via open neighbourhoods.
  have hgoal :
      ∀ U : Set X, IsOpen U → x ∈ U → (U ∩ interior (closure A)).Nonempty := by
    intro U hU hxU
    -- Since `x ∈ closure A`, the open set `U` meets `A`.
    have hUA_nonempty : (U ∩ (A : Set X)).Nonempty := by
      have hmem := (mem_closure_iff).1 hx_closure
      exact hmem U hU hxU
    rcases hUA_nonempty with ⟨y, hyU, hyA⟩
    -- Apply `P1` to the point `y ∈ A`.
    have hy_cl : y ∈ closure (interior A) := hP1 hyA
    -- Therefore `U` meets `interior A`.
    have hU_intA_nonempty : (U ∩ interior A).Nonempty := by
      have hmem_y := (mem_closure_iff).1 hy_cl
      exact hmem_y U hU hyU
    rcases hU_intA_nonempty with ⟨z, hzU, hzIntA⟩
    -- `interior A ⊆ interior (closure A)`.
    have hzIntClA : z ∈ interior (closure A) := by
      have hsubset : interior A ⊆ interior (closure A) :=
        interior_mono (subset_closure : (A : Set X) ⊆ closure A)
      exact hsubset hzIntA
    exact ⟨z, hzU, hzIntClA⟩
  exact (mem_closure_iff).2 hgoal

theorem P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = Set.univ) : Topology.P1 A := by
  intro x hx
  simpa [h] using (Set.mem_univ x)

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = Set.univ) : Topology.P2 A := by
  intro x hx
  simpa [h, interior_univ] using (Set.mem_univ x)

theorem P2_iff_P3_of_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure A = closure (interior A)) : Topology.P2 A ↔ Topology.P3 A := by
  -- Equality of the relevant interiors obtained from the hypothesis on closures
  have h_int_eq : interior (closure A) = interior (closure (interior A)) := by
    simpa using congrArg interior h
  -- Prove the two implications
  constructor
  · intro hP2
    -- `P2 A → P3 A`
    intro x hxA
    have hx : x ∈ interior (closure (interior A)) := hP2 hxA
    simpa [h_int_eq] using hx
  · intro hP3
    -- `P3 A → P2 A`
    intro x hxA
    have hx : x ∈ interior (closure A) := hP3 hxA
    simpa [h_int_eq] using hx

theorem Topology.P2_of_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A → Topology.P3 A → Topology.P2 A := by
  intro hP1 hP3
  -- First, show that `closure A = closure (interior A)` using `hP1`.
  have h_closure_eq : closure (A : Set X) = closure (interior A) := by
    apply le_antisymm
    ·
      have h_subset : (A : Set X) ⊆ closure (interior A) := hP1
      have : closure (A : Set X) ⊆ closure (closure (interior A)) :=
        closure_mono h_subset
      simpa [closure_closure] using this
    ·
      exact closure_mono (interior_subset : interior (A : Set X) ⊆ A)
  -- With this equality, use the equivalence to deduce `P2 A` from `hP3`.
  exact (P2_iff_P3_of_closure_eq (X := X) (A := A) h_closure_eq).2 hP3

theorem Topology.P2_implies_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A → Topology.P1 A ∧ Topology.P3 A := by
  intro hP2
  exact ⟨Topology.P2_implies_P1 (A := A) hP2, Topology.P2_implies_P3 (A := A) hP2⟩

theorem P2_union3 {X : Type*} [TopologicalSpace X] {A B C : Set X} : Topology.P2 A → Topology.P2 B → Topology.P2 C → Topology.P2 (A ∪ B ∪ C) := by
  intro hP2A hP2B hP2C
  -- First, get `P2` for `A ∪ B`.
  have hP2AB : Topology.P2 (A ∪ B) :=
    Topology.P2_union (A := A) (B := B) hP2A hP2B
  -- Then, combine with `C`.
  have hP2ABC : Topology.P2 ((A ∪ B) ∪ C) :=
    Topology.P2_union (A := A ∪ B) (B := C) hP2AB hP2C
  -- Rearrange the unions to match the desired shape.
  simpa [Set.union_assoc] using hP2ABC

theorem P1_closure_eq_self {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A → closure (interior A) = closure A := by
  intro hP1
  apply le_antisymm
  ·
    exact closure_mono (interior_subset : interior (A : Set X) ⊆ A)
  ·
    have hA : (A : Set X) ⊆ closure (interior A) := hP1
    have hclosure : closure (A : Set X) ⊆ closure (closure (interior A)) :=
      closure_mono hA
    simpa [closure_closure] using hclosure

theorem P1_iff_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P1 A ↔ Topology.P3 A := by
  constructor
  · intro _hP1
    exact P3_of_open (A := A) hA
  · intro _hP3
    exact P1_of_open (A := A) hA

theorem P1_univ {X : Type*} [TopologicalSpace X] : Topology.P1 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P3_iff_P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P3 A ↔ Topology.P2 A := by
  constructor
  · intro _hP3
    exact P2_of_open (A := A) hA
  · intro hP2
    exact P2_implies_P3 (A := A) hP2

theorem P2_iff_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A ↔ (Topology.P1 A ∧ Topology.P3 A) := by
  constructor
  · intro hP2
    exact Topology.P2_implies_P1_and_P3 (A := A) hP2
  · rintro ⟨hP1, hP3⟩
    exact Topology.P2_of_P1_and_P3 (A := A) hP1 hP3

theorem P1_of_subset_of_P2 {X : Type*} [TopologicalSpace X] {A B : Set X} (h₁ : Topology.P2 A) (h₂ : A ⊆ B) (h₃ : B ⊆ closure A) : Topology.P1 B := by
  intro x hxB
  -- `x` is in `closure A`
  have hx_clA : x ∈ closure (A : Set X) := h₃ hxB
  -- We show `closure A ⊆ closure (interior B)`
  have h_clA_subset_clIntB : closure (A : Set X) ⊆ closure (interior B) := by
    calc
      closure (A : Set X)
          ⊆ closure (interior A) := by
            -- from `P2 A`, we have `A ⊆ interior (closure (interior A))`
            -- hence, taking closures,
            -- `closure A ⊆ closure (interior (closure (interior A))) = closure (interior A)`
            have hA_sub : (A : Set X) ⊆ interior (closure (interior A)) := h₁
            simpa [closure_closure] using closure_mono hA_sub
      _ ⊆ closure (interior B) := by
            -- since `A ⊆ B`, we have `interior A ⊆ interior B`
            have h_int : (interior A : Set X) ⊆ interior B := interior_mono h₂
            exact closure_mono h_int
  exact h_clA_subset_clIntB hx_clA

theorem P1_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P1 A := by
  intro x hx
  -- In a subsingleton, any nonempty set is the whole universe.
  have hA_univ : (A : Set X) = Set.univ := by
    ext y
    constructor
    · intro _; exact Set.mem_univ y
    · intro _
      have h_eq : y = x := Subsingleton.elim _ _
      simpa [h_eq] using hx
  -- Conclude the required membership.
  simpa [hA_univ, interior_univ, closure_univ] using (Set.mem_univ x)

theorem P2_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P2 A := by
  intro x hx
  -- Since `X` is a subsingleton, any nonempty set is the whole universe.
  have hA_univ : (A : Set X) = Set.univ := by
    ext y
    constructor
    · intro _; exact Set.mem_univ y
    · intro _
      have h_eq : y = x := Subsingleton.elim _ _
      simpa [h_eq] using hx
  -- Conclude the required membership.
  simpa [hA_univ, interior_univ, closure_univ] using (Set.mem_univ x)

theorem P3_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P3 A := by
  intro x hx
  -- In a subsingleton, any nonempty set is the whole universe.
  have hA_univ : (A : Set X) = Set.univ := by
    ext y
    constructor
    · intro _; exact Set.mem_univ y
    · intro _
      have h_eq : y = x := Subsingleton.elim _ _
      simpa [h_eq] using hx
  -- Conclude the required membership.
  simpa [hA_univ, closure_univ, interior_univ] using (Set.mem_univ x)

theorem Topology.P1_compl_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P1 (Aᶜ) := by
  -- The complement of a closed set is open.
  have hOpen : IsOpen (Aᶜ) := by
    simpa [IsClosed] using hA
  -- Apply the lemma for open sets.
  exact P1_of_open (A := Aᶜ) hOpen

theorem Topology.P1_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 (closure (interior A)) := by
  intro x hx
  -- `interior A` is contained in `interior (closure (interior A))`
  have hsubset : (interior A : Set X) ⊆ interior (closure (interior A)) := by
    -- apply monotonicity of `interior` to the inclusion `interior A ⊆ closure (interior A)`
    have h : interior (interior A) ⊆ interior (closure (interior A)) :=
      interior_mono (subset_closure : (interior A : Set X) ⊆ closure (interior A))
    simpa [interior_interior] using h
  -- taking closures gives the desired inclusion of closures
  have hclosure :
      closure (interior A) ⊆ closure (interior (closure (interior A))) :=
    closure_mono hsubset
  exact hclosure hx

theorem P3_compl_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → Topology.P3 (Aᶜ) := by
  intro hA_closed
  have h_open : IsOpen (Aᶜ) := hA_closed.isOpen_compl
  exact P3_of_open (A := Aᶜ) h_open

theorem P1_iff_closure_subset {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ closure (interior A) = closure A := by
  constructor
  · intro hP1
    exact P1_closure_eq_self (A := A) hP1
  · intro hEq
    intro x hx
    have hx_cl : x ∈ closure (A : Set X) := subset_closure hx
    simpa [hEq] using hx_cl

theorem P2_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P2 A → P2 B → P2 (A ×ˢ B) := by
  intro hP2A hP2B
  intro x hx
  -- Decompose the hypothesis `hx : x ∈ A ×ˢ B`.
  rcases hx with ⟨hxA, hxB⟩
  -- Use the `P2` hypotheses on both coordinates.
  have hxA_int : x.1 ∈ interior (closure (interior A)) := hP2A hxA
  have hxB_int : x.2 ∈ interior (closure (interior B)) := hP2B hxB
  -- Define auxiliary neighbourhoods.
  let U : Set X := interior (closure (interior A))
  let V : Set Y := interior (closure (interior B))
  have hUopen : IsOpen U := by
    simpa [U] using isOpen_interior
  have hVopen : IsOpen V := by
    simpa [V] using isOpen_interior
  have hxU : x.1 ∈ U := by
    simpa [U] using hxA_int
  have hxV : x.2 ∈ V := by
    simpa [V] using hxB_int
  -- The open product neighbourhood around `x`.
  have hUV_open : IsOpen (U ×ˢ V) := hUopen.prod hVopen
  have hxUV   : x ∈ U ×ˢ V       := by
    exact ⟨hxU, hxV⟩
  -- Show that this neighbourhood is contained in the required closure.
  have h_subset :
      (U ×ˢ V : Set (X × Y)) ⊆ closure (interior (A ×ˢ B)) := by
    -- Step 1 : `(U ×ˢ V)` is contained in `closure (interior A) ×ˢ closure (interior B)`.
    have h1 :
        (U ×ˢ V : Set (X × Y)) ⊆
          closure (interior A) ×ˢ closure (interior B) := by
      intro y hy
      rcases hy with ⟨hyU, hyV⟩
      have hyA_cl : (y.1) ∈ closure (interior A) := by
        -- `U = interior (closure (interior A))`
        have : y.1 ∈ interior (closure (interior A)) := by
          simpa [U] using hyU
        exact interior_subset this
      have hyB_cl : (y.2) ∈ closure (interior B) := by
        have : y.2 ∈ interior (closure (interior B)) := by
          simpa [V] using hyV
        exact interior_subset this
      exact ⟨hyA_cl, hyB_cl⟩
    -- Step 2 : `closure (interior A) ×ˢ closure (interior B)`
    --         is the same as `closure ((interior A) ×ˢ (interior B))`.
    have h_prod_eq :
        (closure (interior A) ×ˢ closure (interior B) :
            Set (X × Y)) =
          closure ((interior A) ×ˢ (interior B) : Set (X × Y)) := by
      simpa using
        (closure_prod_eq (s := interior A) (t := interior B)).symm
    -- Step 3 : `interior A ×ˢ interior B ⊆ interior (A ×ˢ B)`.
    have h_int_subset :
        ((interior A) ×ˢ (interior B) : Set (X × Y)) ⊆
          interior (A ×ˢ B) := by
      intro y hy
      rcases hy with ⟨hyA, hyB⟩
      -- The open set `interior A ×ˢ interior B` is a neighbourhood of `y`
      -- contained in `A ×ˢ B`, so `y` is in the interior of `A ×ˢ B`.
      have h_open : IsOpen ((interior A) ×ˢ (interior B)) :=
        (isOpen_interior).prod isOpen_interior
      have h_nhds :
          ((interior A) ×ˢ (interior B) : Set (X × Y)) ∈ 𝓝 y :=
        h_open.mem_nhds ⟨hyA, hyB⟩
      have h_subsetAB :
          ((interior A) ×ˢ (interior B) : Set (X × Y)) ⊆ (A ×ˢ B) := by
        intro z hz; exact ⟨interior_subset hz.1, interior_subset hz.2⟩
      have h_nhds_AB : (A ×ˢ B : Set (X × Y)) ∈ 𝓝 y :=
        Filter.mem_of_superset h_nhds h_subsetAB
      exact (mem_interior_iff_mem_nhds).2 h_nhds_AB
    -- Step 4 : put everything together.
    have h2 :
        closure ((interior A) ×ˢ (interior B) : Set (X × Y))
          ⊆ closure (interior (A ×ˢ B)) :=
      closure_mono h_int_subset
    intro y hy
    have : y ∈
        closure ((interior A) ×ˢ (interior B) : Set (X × Y)) := by
      -- From `h1` and `h_prod_eq`.
      have : y ∈ closure (interior A) ×ˢ closure (interior B) := h1 hy
      simpa [h_prod_eq] using this
    exact h2 this
  -- Turn neighbourhood information into membership of the interior.
  have h_cl_nhds :
      (closure (interior (A ×ˢ B)) : Set (X × Y)) ∈ 𝓝 x :=
    Filter.mem_of_superset (hUV_open.mem_nhds hxUV) h_subset
  exact (mem_interior_iff_mem_nhds).2 h_cl_nhds

theorem P3_proj_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {S : Set (X × Y)} : P3 S → P3 (Prod.fst '' S) := by
  intro hP3S
  intro x hx
  -- Choose a point `p ∈ S` whose first coordinate is `x = p.1`.
  rcases hx with ⟨p, hpS, rfl⟩
  -- From `hP3S` we get `p ∈ interior (closure S)`.
  have hp_int : (p : X × Y) ∈ interior (closure S) := hP3S hpS
  -- View this as a neighbourhood of `p`.
  have h_int_nhds : (interior (closure S) : Set (X × Y)) ∈ 𝓝 p :=
    isOpen_interior.mem_nhds hp_int
  -- Split this product‐neighbourhood.
  rcases (mem_nhds_prod_iff).1 h_int_nhds with
    ⟨U, hU_nhds, V, hV_nhds, hUV_subset⟩
  -- `p.2` lies in `V`.
  have hpV : p.2 ∈ V := mem_of_mem_nhds hV_nhds
  -- Replace `V` by an *open* set `V' ⊆ V` still containing `p.2`.
  rcases (mem_nhds_iff.1 hV_nhds) with ⟨V', hV'subV, hV'open, hpV'⟩
  -- Show: every `z ∈ U` belongs to `closure (Prod.fst '' S)`.
  have hU_subset_closure : (U : Set X) ⊆ closure (Prod.fst '' S) := by
    intro z hzU
    -- `(z, p.2)` is in `interior (closure S)` (hence in `closure S`).
    have hz_int : (z, p.2) ∈ interior (closure S) :=
      hUV_subset ⟨hzU, hpV⟩
    have hz_cl : (z, p.2) ∈ closure S := interior_subset hz_int
    -- Use the neighbourhood characterisation of `closure`.
    have : z ∈ closure (Prod.fst '' S) := by
      refine (mem_closure_iff).2 ?_
      intro W hWopen hzW
      -- Consider the open product `W ×ˢ V'`.
      have hPopen : IsOpen (W ×ˢ V') := hWopen.prod hV'open
      have hzP : (z, p.2) ∈ W ×ˢ V' := by
        exact ⟨hzW, hpV'⟩
      -- `S` meets this open neighbourhood.
      have h_nonempty : ((W ×ˢ V') ∩ S).Nonempty :=
        (mem_closure_iff).1 hz_cl _ hPopen hzP
      rcases h_nonempty with ⟨r, ⟨hrP, hrS⟩⟩
      rcases hrP with ⟨hrW, _hrV⟩
      exact ⟨r.1, ⟨hrW, ⟨r, hrS, rfl⟩⟩⟩
    exact this
  -- Hence `closure (Prod.fst '' S)` is a neighbourhood of `p.1`.
  have h_closure_nhds : (closure (Prod.fst '' S) : Set X) ∈ 𝓝 p.1 :=
    Filter.mem_of_superset hU_nhds hU_subset_closure
  -- Conclude `p.1 ∈ interior (closure (Prod.fst '' S))`.
  exact (mem_interior_iff_mem_nhds).2 h_closure_nhds

theorem P3_bot {X : Type*} [TopologicalSpace X] : P3 (∅ : Set X) ↔ True := by
  constructor
  · intro _; trivial
  · intro _; intro x hx; cases hx

theorem P2_top {X : Type*} [TopologicalSpace X] : P2 (Set.univ : Set X) ↔ True := by
  constructor
  · intro _; trivial
  · intro _; exact P2_univ (X := X)

theorem P1_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P1 A → P1 B → P1 (A ×ˢ B) := by
  intro hP1A hP1B
  intro x hx
  rcases hx with ⟨hxA, hxB⟩
  -- Use the `P1` hypotheses on both coordinates.
  have hxA_cl : x.1 ∈ closure (interior A) := hP1A hxA
  have hxB_cl : x.2 ∈ closure (interior B) := hP1B hxB
  -- Put the point into the product of the two closures.
  have hx_prod : (x : X × Y) ∈
      (closure (interior A) ×ˢ closure (interior B)) := by
    exact ⟨hxA_cl, hxB_cl⟩
  -- Show that this product is contained in the desired closure.
  have h_subset :
      (closure (interior A) ×ˢ closure (interior B) : Set (X × Y)) ⊆
        closure (interior (A ×ˢ B)) := by
    -- First, relate the product of closures to the closure of the product.
    have h_prod_eq :
        (closure (interior A) ×ˢ closure (interior B) : Set (X × Y)) =
          closure ((interior A) ×ˢ (interior B) : Set (X × Y)) := by
      simpa using
        (closure_prod_eq (s := interior A) (t := interior B)).symm
    -- Next, show that `interior A ×ˢ interior B ⊆ interior (A ×ˢ B)`.
    have h_int_subset :
        ((interior A) ×ˢ (interior B) : Set (X × Y)) ⊆
          interior (A ×ˢ B) := by
      intro y hy
      rcases hy with ⟨hyA, hyB⟩
      -- The open set `interior A ×ˢ interior B` is a neighbourhood of `y`
      -- contained in `A ×ˢ B`, so `y` is in the interior of `A ×ˢ B`.
      have h_open : IsOpen ((interior A) ×ˢ (interior B)) :=
        (isOpen_interior).prod isOpen_interior
      have h_nhds :
          ((interior A) ×ˢ (interior B) : Set (X × Y)) ∈ 𝓝 y :=
        h_open.mem_nhds ⟨hyA, hyB⟩
      have h_subsetAB :
          ((interior A) ×ˢ (interior B) : Set (X × Y)) ⊆ (A ×ˢ B) := by
        intro z hz
        exact ⟨interior_subset hz.1, interior_subset hz.2⟩
      have h_nhds_AB : (A ×ˢ B : Set (X × Y)) ∈ 𝓝 y :=
        Filter.mem_of_superset h_nhds h_subsetAB
      exact (mem_interior_iff_mem_nhds).2 h_nhds_AB
    -- Taking closures yields the required inclusion.
    have h_closure_subset :
        closure ((interior A) ×ˢ (interior B) : Set (X × Y)) ⊆
          closure (interior (A ×ˢ B)) :=
      closure_mono h_int_subset
    simpa [h_prod_eq] using h_closure_subset
  -- Conclude the proof.
  exact h_subset hx_prod

theorem P3_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P3 A → P3 B → P3 (A ×ˢ B) := by
  intro hP3A hP3B
  intro x hx
  rcases hx with ⟨hxA, hxB⟩
  -- points are in the interior of the respective closures
  have hxA_int : x.1 ∈ interior (closure (A : Set X)) := hP3A hxA
  have hxB_int : x.2 ∈ interior (closure (B : Set Y)) := hP3B hxB
  -- the product of these interiors is an open neighbourhood of `x`
  have hU_open : IsOpen (interior (closure (A : Set X))) := isOpen_interior
  have hV_open : IsOpen (interior (closure (B : Set Y))) := isOpen_interior
  have hxUV : (x : X × Y) ∈
      (interior (closure (A : Set X)) ×ˢ interior (closure (B : Set Y))) := by
    exact ⟨hxA_int, hxB_int⟩
  -- this neighbourhood is contained in `closure (A ×ˢ B)`
  have h_subset :
      (interior (closure (A : Set X)) ×ˢ interior (closure (B : Set Y)) :
        Set (X × Y)) ⊆ closure (A ×ˢ B) := by
    intro y hy
    rcases hy with ⟨hyA_int, hyB_int⟩
    have hyA : y.1 ∈ closure (A : Set X) := interior_subset hyA_int
    have hyB : y.2 ∈ closure (B : Set Y) := interior_subset hyB_int
    have h_in : (y : X × Y) ∈
        (closure (A : Set X) ×ˢ closure (B : Set Y)) := ⟨hyA, hyB⟩
    have h_eq :
        (closure (A : Set X) ×ˢ closure (B : Set Y) : Set (X × Y)) =
          closure (A ×ˢ B) := by
      simpa using (closure_prod_eq (s := A) (t := B)).symm
    simpa [h_eq] using h_in
  -- turn the neighbourhood information into membership of the interior
  have h_open_prod :
      IsOpen (interior (closure (A : Set X)) ×ˢ interior (closure (B : Set Y))) :=
    hU_open.prod hV_open
  have h_nhds :
      ((interior (closure (A : Set X)) ×ˢ interior (closure (B : Set Y))) :
        Set (X × Y)) ∈ 𝓝 x :=
    h_open_prod.mem_nhds hxUV
  have h_nhds_closure : (closure (A ×ˢ B) : Set (X × Y)) ∈ 𝓝 x :=
    Filter.mem_of_superset h_nhds h_subset
  exact (mem_interior_iff_mem_nhds).2 h_nhds_closure

theorem P2_proj_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {S : Set (X × Y)} : P2 S → P2 (Prod.fst '' S) := by
  intro hP2S
  intro x hx
  -- choose a point `p ∈ S` with first coordinate `x`
  rcases hx with ⟨p, hpS, rfl⟩
  -- `p` lies in the interior of `closure (interior S)`
  have hp_int : (p : X × Y) ∈ interior (closure (interior S)) := hP2S hpS
  -- view this as a neighbourhood of `p`
  have h_int_nhds :
      (interior (closure (interior S)) : Set (X × Y)) ∈ 𝓝 p :=
    isOpen_interior.mem_nhds hp_int
  -- split the product neighbourhood
  rcases (mem_nhds_prod_iff).1 h_int_nhds with
    ⟨U, hU_nhds, V, hV_nhds, hUV_subset⟩
  -- make `V` open and still containing `p.2`
  rcases (mem_nhds_iff).1 hV_nhds with ⟨V', hV'sub, hV'open, hpV'⟩
  have hpV : p.2 ∈ V := mem_of_mem_nhds hV_nhds
  ------------------------------------------------------------------
  -- Main claim:  `U ⊆ closure (Prod.fst '' interior S)`
  ------------------------------------------------------------------
  have hU_subset₁ : (U : Set X) ⊆ closure (Prod.fst '' interior S) := by
    intro z hzU
    -- `(z , p.2)` is in the closure of `interior S`
    have hz_cl : (z, p.2) ∈ closure (interior S) := by
      have hz_in_int :
          (z, p.2) ∈ interior (closure (interior S)) :=
        hUV_subset ⟨hzU, hpV⟩
      exact interior_subset hz_in_int
    -- prove `z ∈ closure (Prod.fst '' interior S)`
    have : z ∈ closure (Prod.fst '' interior S) := by
      refine (mem_closure_iff).2 ?_
      intro W hWopen hzW
      -- consider the open product `W ×ˢ V'`
      have hProd_open : IsOpen (W ×ˢ V') := hWopen.prod hV'open
      have hzProd : (z, p.2) ∈ W ×ˢ V' := by
        exact ⟨hzW, hpV'⟩
      -- `interior S` meets this neighbourhood
      have h_nonempty :
          ((W ×ˢ V') ∩ interior S).Nonempty :=
        (mem_closure_iff).1 hz_cl _ hProd_open hzProd
      rcases h_nonempty with ⟨r, hrWV', hr_intS⟩
      rcases hrWV' with ⟨hrW, _hrV'⟩
      exact ⟨r.1, ⟨hrW, ⟨r, hr_intS, rfl⟩⟩⟩
    exact this
  ------------------------------------------------------------------
  -- `Prod.fst '' interior S` is open
  ------------------------------------------------------------------
  have h_open_image_intS :
      IsOpen (Prod.fst '' interior S : Set X) := by
    have hf : IsOpenMap (fun q : X × Y => q.1) := isOpenMap_fst
    simpa using hf _ isOpen_interior
  ------------------------------------------------------------------
  -- hence it lies inside `interior (Prod.fst '' S)`
  ------------------------------------------------------------------
  have h_image_subset :
      (Prod.fst '' interior S : Set X) ⊆ interior (Prod.fst '' S) := by
    intro z hz
    have hz_nhds :
        (Prod.fst '' interior S : Set X) ∈ 𝓝 z :=
      h_open_image_intS.mem_nhds hz
    -- this image is contained in `Prod.fst '' S`
    have h_sub : (Prod.fst '' interior S : Set X) ⊆ Prod.fst '' S := by
      intro y hy
      rcases hy with ⟨r, hr_int, rfl⟩
      exact ⟨r, interior_subset hr_int, rfl⟩
    have h_nhds :
        (Prod.fst '' S : Set X) ∈ 𝓝 z :=
      Filter.mem_of_superset hz_nhds h_sub
    exact (mem_interior_iff_mem_nhds).2 h_nhds
  -- passing to closures
  have h_closure_subset :
      closure (Prod.fst '' interior S : Set X) ⊆
        closure (interior (Prod.fst '' S)) :=
    closure_mono h_image_subset
  -- thus `U` is contained in `closure (interior (Prod.fst '' S))`
  have hU_subset :
      (U : Set X) ⊆ closure (interior (Prod.fst '' S)) :=
    Set.Subset.trans hU_subset₁ h_closure_subset
  ------------------------------------------------------------------
  -- so `closure (interior (Prod.fst '' S))` is a neighbourhood of `p.1`
  ------------------------------------------------------------------
  have h_nhds :
      (closure (interior (Prod.fst '' S)) : Set X) ∈ 𝓝 p.1 :=
    Filter.mem_of_superset hU_nhds hU_subset
  -- conclude the desired membership
  exact (mem_interior_iff_mem_nhds).2 h_nhds

theorem P2_proj_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {S : Set (X × Y)} : P2 S → P2 (Prod.snd '' S) := by
  intro hP2S
  intro y hy
  -- choose a point `p ∈ S` whose second coordinate is `y`
  rcases hy with ⟨p, hpS, rfl⟩
  -- from `P2` we get `p ∈ interior (closure (interior S))`
  have hp_int : (p : X × Y) ∈ interior (closure (interior S)) := hP2S hpS
  -- view this as a neighbourhood of `p`
  have h_int_nhds :
      (interior (closure (interior S)) : Set (X × Y)) ∈ 𝓝 p :=
    isOpen_interior.mem_nhds hp_int
  -- split this product‐neighbourhood
  rcases (mem_nhds_prod_iff).1 h_int_nhds with
    ⟨U, hU_nhds, V, hV_nhds, hUV_subset⟩
  -- refine `U` to an *open* set `U' ⊆ U` still containing `p.1`
  rcases (mem_nhds_iff.1 hU_nhds) with ⟨U', hU'sub, hU'open, hpU'⟩
  have hpU : p.1 ∈ U := mem_of_mem_nhds hU_nhds
  have hpV : p.2 ∈ V := mem_of_mem_nhds hV_nhds
  ------------------------------------------------------------------
  -- Main claim:  `V ⊆ closure (Prod.snd '' interior S)`
  ------------------------------------------------------------------
  have hV_subset₁ :
      (V : Set Y) ⊆ closure (Prod.snd '' interior S) := by
    intro z hzV
    -- `(p.1 , z)` is in `interior (closure (interior S))`
    have hz_int :
        (p.1, z) ∈ interior (closure (interior S)) :=
      hUV_subset ⟨hpU, hzV⟩
    have hz_cl : (p.1, z) ∈ closure (interior S) := interior_subset hz_int
    -- prove `z ∈ closure (Prod.snd '' interior S)`
    have : z ∈ closure (Prod.snd '' interior S) := by
      refine (mem_closure_iff).2 ?_
      intro W hWopen hzW
      -- consider the open product `U' ×ˢ W`
      have hProd_open : IsOpen (U' ×ˢ W) := hU'open.prod hWopen
      have hzProd : (p.1, z) ∈ U' ×ˢ W := by
        exact ⟨hpU', hzW⟩
      -- `interior S` meets this neighbourhood
      have h_nonempty :
          ((U' ×ˢ W) ∩ interior S).Nonempty :=
        (mem_closure_iff).1 hz_cl _ hProd_open hzProd
      rcases h_nonempty with ⟨r, hrProd, hr_intS⟩
      rcases hrProd with ⟨hrU', hrW⟩
      exact ⟨r.2, ⟨hrW, ⟨r, hr_intS, rfl⟩⟩⟩
    exact this
  ------------------------------------------------------------------
  -- `Prod.snd '' interior S` is open
  ------------------------------------------------------------------
  have h_open_image_intS :
      IsOpen (Prod.snd '' interior S : Set Y) := by
    have hf : IsOpenMap (fun q : X × Y => q.2) := isOpenMap_snd
    simpa using hf _ isOpen_interior
  ------------------------------------------------------------------
  -- hence it lies inside `interior (Prod.snd '' S)`
  ------------------------------------------------------------------
  have h_image_subset :
      (Prod.snd '' interior S : Set Y) ⊆ interior (Prod.snd '' S) := by
    intro z hz
    have hz_nhds :
        (Prod.snd '' interior S : Set Y) ∈ 𝓝 z :=
      h_open_image_intS.mem_nhds hz
    -- this image is contained in `Prod.snd '' S`
    have h_sub : (Prod.snd '' interior S : Set Y) ⊆ Prod.snd '' S := by
      intro y hy
      rcases hy with ⟨r, hr_int, rfl⟩
      exact ⟨r, interior_subset hr_int, rfl⟩
    have h_nhds :
        (Prod.snd '' S : Set Y) ∈ 𝓝 z :=
      Filter.mem_of_superset hz_nhds h_sub
    exact (mem_interior_iff_mem_nhds).2 h_nhds
  -- passing to closures
  have h_closure_subset :
      closure (Prod.snd '' interior S : Set Y) ⊆
        closure (interior (Prod.snd '' S)) :=
    closure_mono h_image_subset
  -- thus `V` is contained in `closure (interior (Prod.snd '' S))`
  have hV_subset :
      (V : Set Y) ⊆ closure (interior (Prod.snd '' S)) :=
    Set.Subset.trans hV_subset₁ h_closure_subset
  ------------------------------------------------------------------
  -- so `closure (interior (Prod.snd '' S))` is a neighbourhood of `p.2`
  ------------------------------------------------------------------
  have h_nhds :
      (closure (interior (Prod.snd '' S)) : Set Y) ∈ 𝓝 p.2 :=
    Filter.mem_of_superset hV_nhds hV_subset
  -- conclude the desired membership
  exact (mem_interior_iff_mem_nhds).2 h_nhds

theorem P3_proj_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {S : Set (X × Y)} : P3 S → P3 (Prod.snd '' S) := by
  intro hP3S
  intro y hy
  -- Choose a point `p ∈ S` whose second coordinate is `y = p.2`.
  rcases hy with ⟨p, hpS, rfl⟩
  -- From `hP3S` we get `p ∈ interior (closure S)`.
  have hp_int : (p : X × Y) ∈ interior (closure S) := hP3S hpS
  -- Regard this as a neighbourhood of `p`.
  have h_int_nhds : (interior (closure S) : Set (X × Y)) ∈ 𝓝 p :=
    isOpen_interior.mem_nhds hp_int
  -- Split this product neighbourhood.
  rcases (mem_nhds_prod_iff).1 h_int_nhds with
    ⟨U, hU_nhds, V, hV_nhds, hUV_subset⟩
  have hpU : p.1 ∈ U := mem_of_mem_nhds hU_nhds
  have hpV : p.2 ∈ V := mem_of_mem_nhds hV_nhds
  -- Shrink `U` to an open set `U' ⊆ U` still containing `p.1`.
  rcases (mem_nhds_iff.1 hU_nhds) with ⟨U', hU'sub, hU'open, hpU'⟩
  ----------------------------------------------------------------
  -- Claim: `V ⊆ closure (Prod.snd '' S)`.
  ----------------------------------------------------------------
  have hV_subset : (V : Set Y) ⊆ closure (Prod.snd '' S) := by
    intro z hzV
    -- `(p.1, z)` belongs to `interior (closure S)` and hence to `closure S`.
    have hz_int : (p.1, z) ∈ interior (closure S) :=
      hUV_subset ⟨hpU, hzV⟩
    have hz_cl : (p.1, z) ∈ closure S := interior_subset hz_int
    -- Show `z ∈ closure (Prod.snd '' S)`.
    have : z ∈ closure (Prod.snd '' S) := by
      refine (mem_closure_iff).2 ?_
      intro W hWopen hzW
      -- Consider the open product `U' ×ˢ W`.
      have hProd_open : IsOpen (U' ×ˢ W) := hU'open.prod hWopen
      have hzProd : (p.1, z) ∈ U' ×ˢ W := by
        exact ⟨hpU', hzW⟩
      -- Since `(p.1, z)` is in the closure of `S`, this neighbourhood meets `S`.
      have h_nonempty : ((U' ×ˢ W) ∩ S).Nonempty :=
        (mem_closure_iff).1 hz_cl _ hProd_open hzProd
      rcases h_nonempty with ⟨q, hqProd, hqS⟩
      rcases hqProd with ⟨hqU', hqW⟩
      exact ⟨q.2, ⟨hqW, ⟨q, hqS, rfl⟩⟩⟩
    exact this
  -- Thus `closure (Prod.snd '' S)` is a neighbourhood of `p.2`.
  have h_closure_nhds : (closure (Prod.snd '' S) : Set Y) ∈ 𝓝 p.2 :=
    Filter.mem_of_superset hV_nhds hV_subset
  -- Conclude that `p.2 ∈ interior (closure (Prod.snd '' S))`.
  exact (mem_interior_iff_mem_nhds).2 h_closure_nhds

theorem P1_union3 {X : Type*} [TopologicalSpace X] {A B C : Set X} : P1 A → P1 B → P1 C → P1 (A ∪ B ∪ C) := by
  intro hP1A hP1B hP1C
  -- Combine `A` and `B` first.
  have hP1AB : P1 (A ∪ B) := P1_union (A := A) (B := B) hP1A hP1B
  -- Then combine the result with `C`.
  have hP1ABC : P1 ((A ∪ B) ∪ C) := P1_union (A := A ∪ B) (B := C) hP1AB hP1C
  simpa [Set.union_assoc] using hP1ABC

theorem P3_union3 {X : Type*} [TopologicalSpace X] {A B C : Set X} : P3 A → P3 B → P3 C → P3 (A ∪ B ∪ C) := by
  intro hP3A hP3B hP3C
  -- First combine `A` and `B`.
  have hP3AB : Topology.P3 (A ∪ B) :=
    Topology.P3_union (A := A) (B := B) hP3A hP3B
  -- Then combine the result with `C`.
  have hP3ABC : Topology.P3 ((A ∪ B) ∪ C) :=
    Topology.P3_union (A := A ∪ B) (B := C) hP3AB hP3C
  simpa [Set.union_assoc] using hP3ABC

theorem P1_of_P3_and_open {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → P3 A → P1 A := by
  intro hA_open hP3
  exact P1_of_open (A := A) hA_open

theorem P2_iUnion_finset {X : Type*} [TopologicalSpace X] {ι : Type*} [Fintype ι] {A : ι → Set X} : (∀ i, P2 (A i)) → P2 (⋃ i, A i) := by
  intro hP2
  simpa using (Topology.P2_iUnion (X := X) (A := A) hP2)

theorem P1_closure_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : P3 A → P1 (closure A) := by
  intro hP3
  intro x hx_cl
  have hsubset : (A : Set X) ⊆ interior (closure A) := hP3
  have hclosure_subset :
      (closure (A : Set X)) ⊆ closure (interior (closure A)) :=
    closure_mono hsubset
  exact hclosure_subset hx_cl

theorem P1_closed_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → Topology.P3 A → Topology.P1 A := by
  intro hClosed hP3
  intro x hxA
  -- `P3` gives that `x` is in the interior of `closure A`, but `closure A = A` since `A` is closed.
  have hxInt : x ∈ interior A := by
    simpa [hClosed.closure_eq] using (hP3 hxA)
  -- Any point of `interior A` lies in `closure (interior A)`.
  exact subset_closure hxInt

theorem P1_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} : Topology.P1 A → Topology.P1 (e '' A) := by
  intro hP1
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- `P1` gives a point of the closure of `interior A`.
  have hx_cl : x ∈ closure (interior A) := hP1 hxA
  -- Apply the homeomorphism.
  have h_in : (e x : Y) ∈ e '' closure (interior A) := ⟨x, hx_cl, rfl⟩
  -- A homeomorphism sends closures to closures.
  have h_image_closure :
      (e '' closure (interior A) : Set Y) = closure (e '' interior A) := by
    simpa using e.image_closure (interior A)
  have h1 : (e x : Y) ∈ closure (e '' interior A) := by
    simpa [h_image_closure] using h_in
  -- A homeomorphism sends interiors to interiors.
  have h_image_interior :
      (e '' interior A : Set Y) = interior (e '' A) := by
    simpa using e.image_interior A
  simpa [h_image_interior] using h1

theorem P2_prod_univ_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : Topology.P2 A → Topology.P2 (A ×ˢ (Set.univ : Set Y)) := by
  intro hP2A
  apply P2_prod (A := A) (B := (Set.univ : Set Y))
  · exact hP2A
  · exact P2_univ (X := Y)

theorem P2_union_iInter {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} (h : ∀ i, Topology.P2 (A i)) : Topology.P2 (⋃ i, interior (A i)) := by
  -- Each `interior (A i)` satisfies `P2`.
  have hP2_int : ∀ i, Topology.P2 (interior (A i)) := by
    intro i
    simpa using (Topology.P2_interior (A := A i))
  -- Apply `P2_iUnion` to the family `interior (A i)`.
  simpa using
    (Topology.P2_iUnion (X := X) (A := fun i => interior (A i)) hP2_int)

theorem P3_prod_univ_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} : Topology.P3 B → Topology.P3 ((Set.univ : Set X) ×ˢ B) := by
  intro hP3B
  have hP3_univ : Topology.P3 (Set.univ : Set X) := by
    simpa using (Topology.P3_univ (X := X))
  simpa using
    (Topology.P3_prod (A := (Set.univ : Set X)) (B := B) hP3_univ hP3B)

theorem P1_prod_univ_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} : Topology.P1 B → Topology.P1 ((Set.univ : Set X) ×ˢ B) := by
  intro hP1B
  have hP1_univ : P1 (Set.univ : Set X) := by
    simpa using (P1_univ (X := X))
  simpa using
    (P1_prod (A := (Set.univ : Set X)) (B := B) hP1_univ hP1B)

theorem P2_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} : Topology.P2 A → Topology.P2 (e '' A) := by
  intro hP2
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- Apply `P2` to obtain a point in the required interior.
  have hx : x ∈ interior (closure (interior A)) := hP2 hxA
  -- Transport this fact through the homeomorphism `e`.
  have h1 : (e x : Y) ∈ interior (e '' closure (interior A)) := by
    have : (e x : Y) ∈ (e '' interior (closure (interior A))) := ⟨x, hx, rfl⟩
    simpa [e.image_interior (closure (interior A))] using this
  -- Rewrite the set using the fact that `e` sends closures to closures.
  have h2 : (e x : Y) ∈ interior (closure (e '' interior A)) := by
    simpa [e.image_closure (interior A)] using h1
  -- Rewrite once more using the fact that `e` sends interiors to interiors.
  have h3 : (e x : Y) ∈ interior (closure (interior (e '' A))) := by
    simpa [e.image_interior A] using h2
  exact h3

theorem P3_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} : Topology.P3 A → Topology.P3 (e '' A) := by
  intro hP3
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- `hP3` gives the required interior point on `X`.
  have hx : x ∈ interior (closure (A : Set X)) := hP3 hxA
  -- Transport through the homeomorphism.
  have h1 : (e x : Y) ∈ interior (e '' closure (A : Set X)) := by
    have : (e x : Y) ∈ (e '' interior (closure (A : Set X))) := ⟨x, hx, rfl⟩
    simpa [e.image_interior (closure (A : Set X))] using this
  -- Rewrite using the fact that `e` sends closures to closures.
  simpa [e.image_closure (A : Set X)] using h1

theorem P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P3 (closure A) → Topology.P3 A := by
  intro hP3
  intro x hxA
  have hx_cl : x ∈ closure (A : Set X) := subset_closure hxA
  simpa [closure_closure] using hP3 hx_cl

theorem P2_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} : Topology.P2 B → Topology.P2 (e ⁻¹' B) := by
  intro hP2B
  -- First, transport `P2 B` along the inverse homeomorphism.
  have hImage : Topology.P2 (e.symm '' B) := by
    have h := P2_image_homeomorph (e := e.symm) (A := B) hP2B
    simpa using h
  -- `e.symm '' B` coincides with the preimage `e ⁻¹' B`.
  have h_eq : (e.symm '' B : Set X) = e ⁻¹' B := by
    ext x
    constructor
    · rintro ⟨y, hyB, rfl⟩
      -- `e (e.symm y) = y ∈ B`
      simpa using hyB
    · intro hx
      refine ⟨e x, hx, ?_⟩
      simpa using (e.symm_apply_apply x)
  -- Now prove `P2 (e ⁻¹' B)`.
  intro x hx
  -- View `x` as an element of `e.symm '' B`.
  have hx_image : x ∈ e.symm '' B := by
    refine ⟨e x, ?_, ?_⟩
    · simpa using hx
    · simpa using (e.symm_apply_apply x)
  -- Apply `P2` for `e.symm '' B`.
  have hx_int : x ∈ interior (closure (interior (e.symm '' B))) :=
    hImage hx_image
  -- Re‐express the set using the equality `h_eq`.
  simpa [h_eq] using hx_int

theorem P1_proj_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {S : Set (X × Y)} : Topology.P1 S → Topology.P1 (Prod.fst '' S) := by
  intro hP1S
  intro x hx
  rcases hx with ⟨p, hpS, rfl⟩
  -- `p` lies in the closure of the interior of `S`.
  have hp_cl : (p : X × Y) ∈ closure (interior S) := hP1S hpS
  ------------------------------------------------------------------
  -- Step 1:  show `p.1 ∈ closure (Prod.fst '' interior S)`
  ------------------------------------------------------------------
  have hp1_cl : p.1 ∈ closure (Prod.fst '' interior S) := by
    refine (mem_closure_iff).2 ?_
    intro U hUopen hpU
    -- Consider the open product neighbourhood `U ×ˢ univ`.
    have h_open_prod : IsOpen (U ×ˢ (Set.univ : Set Y)) :=
      hUopen.prod isOpen_univ
    have hp_mem_prod : (p : X × Y) ∈ U ×ˢ (Set.univ : Set Y) := by
      exact ⟨hpU, by simp⟩
    -- `interior S` meets this neighbourhood.
    have h_nonempty :
        ((U ×ˢ (Set.univ : Set Y)) ∩ interior S).Nonempty :=
      (mem_closure_iff).1 hp_cl _ h_open_prod hp_mem_prod
    rcases h_nonempty with ⟨q, hqProd, hqInt⟩
    rcases hqProd with ⟨hqU, _hqV⟩
    -- Produce a witness in `U ∩ Prod.fst '' interior S`.
    refine ⟨q.1, ?_⟩
    have hq_image : (q.1) ∈ Prod.fst '' interior S := ⟨q, hqInt, rfl⟩
    exact ⟨hqU, hq_image⟩
  ------------------------------------------------------------------
  -- Step 2:  relate the two closures.
  ------------------------------------------------------------------
  have h_closure_subset :
      closure (Prod.fst '' interior S : Set X) ⊆
        closure (interior (Prod.fst '' S)) := by
    -- First, `Prod.fst '' interior S ⊆ interior (Prod.fst '' S)`.
    have h_image_subset :
        (Prod.fst '' interior S : Set X) ⊆ interior (Prod.fst '' S) := by
      intro z hz
      -- `Prod.fst '' interior S` is open.
      have h_open_image : IsOpen (Prod.fst '' interior S : Set X) := by
        have hOpenMap : IsOpenMap (fun q : X × Y => q.1) := isOpenMap_fst
        simpa using hOpenMap _ isOpen_interior
      -- Hence it is a neighbourhood of `z`.
      have hz_nhds : (Prod.fst '' interior S : Set X) ∈ 𝓝 z :=
        h_open_image.mem_nhds hz
      -- It is contained in `Prod.fst '' S`.
      have h_sub : (Prod.fst '' interior S : Set X) ⊆ Prod.fst '' S := by
        intro y hy
        rcases hy with ⟨q, hqInt, rfl⟩
        exact ⟨q, interior_subset hqInt, rfl⟩
      have h_nhds : (Prod.fst '' S : Set X) ∈ 𝓝 z :=
        Filter.mem_of_superset hz_nhds h_sub
      -- Therefore `z` lies in the interior of `Prod.fst '' S`.
      exact (mem_interior_iff_mem_nhds).2 h_nhds
    -- Taking closures yields the required inclusion.
    exact closure_mono h_image_subset
  ------------------------------------------------------------------
  -- Final step: combine the two facts.
  ------------------------------------------------------------------
  exact h_closure_subset hp1_cl

theorem P1_proj_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {S : Set (X × Y)} : Topology.P1 S → Topology.P1 (Prod.snd '' S) := by
  intro hP1S
  intro y hy
  rcases hy with ⟨p, hpS, rfl⟩
  -- `p` lies in the closure of the interior of `S`.
  have hp_cl : (p : X × Y) ∈ closure (interior S) := hP1S hpS
  ------------------------------------------------------------------
  -- Step 1:  show `p.2 ∈ closure (Prod.snd '' interior S)`
  ------------------------------------------------------------------
  have hp2_cl : p.2 ∈ closure (Prod.snd '' interior S) := by
    refine (mem_closure_iff).2 ?_
    intro V hVopen hpV
    -- Consider the open product neighbourhood `univ ×ˢ V`.
    have h_open_prod : IsOpen ((Set.univ : Set X) ×ˢ V) :=
      isOpen_univ.prod hVopen
    have hp_mem_prod : (p : X × Y) ∈ (Set.univ : Set X) ×ˢ V := by
      exact ⟨by simp, hpV⟩
    -- `interior S` meets this neighbourhood.
    have h_nonempty :
        (((Set.univ : Set X) ×ˢ V) ∩ interior S).Nonempty :=
      (mem_closure_iff).1 hp_cl _ h_open_prod hp_mem_prod
    rcases h_nonempty with ⟨q, hqProd, hqInt⟩
    rcases hqProd with ⟨_hqU, hqV⟩
    -- Produce a witness in `V ∩ Prod.snd '' interior S`.
    exact ⟨q.2, ⟨hqV, ⟨q, hqInt, rfl⟩⟩⟩
  ------------------------------------------------------------------
  -- Step 2:  relate the two closures.
  ------------------------------------------------------------------
  have h_closure_subset :
      closure (Prod.snd '' interior S : Set Y) ⊆
        closure (interior (Prod.snd '' S)) := by
    -- First, `Prod.snd '' interior S ⊆ interior (Prod.snd '' S)`.
    have h_image_subset :
        (Prod.snd '' interior S : Set Y) ⊆ interior (Prod.snd '' S) := by
      intro z hz
      -- `Prod.snd '' interior S` is open.
      have h_open_image : IsOpen (Prod.snd '' interior S : Set Y) := by
        have hOpenMap : IsOpenMap (fun q : X × Y => q.2) := isOpenMap_snd
        simpa using hOpenMap _ isOpen_interior
      -- Hence it is a neighbourhood of `z`.
      have hz_nhds : (Prod.snd '' interior S : Set Y) ∈ 𝓝 z :=
        h_open_image.mem_nhds hz
      -- It is contained in `Prod.snd '' S`.
      have h_sub : (Prod.snd '' interior S : Set Y) ⊆ Prod.snd '' S := by
        intro w hw
        rcases hw with ⟨q, hqInt, rfl⟩
        exact ⟨q, interior_subset hqInt, rfl⟩
      have h_nhds : (Prod.snd '' S : Set Y) ∈ 𝓝 z :=
        Filter.mem_of_superset hz_nhds h_sub
      -- Therefore `z` lies in the interior of `Prod.snd '' S`.
      exact (mem_interior_iff_mem_nhds).2 h_nhds
    -- Taking closures yields the required inclusion.
    exact closure_mono h_image_subset
  ------------------------------------------------------------------
  -- Final step: combine the two facts.
  ------------------------------------------------------------------
  exact h_closure_subset hp2_cl

theorem P1_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} : Topology.P1 B → Topology.P1 (e ⁻¹' B) := by
  intro hP1B
  -- 1. Transport `P1 B` along the inverse homeomorphism `e.symm`.
  have hImage : Topology.P1 (e.symm '' B) := by
    simpa using
      (P1_image_homeomorph (e := e.symm) (A := B) hP1B)
  -- 2. Identify `e.symm '' B` with the preimage `e ⁻¹' B`.
  have h_eq : (e.symm '' B : Set X) = e ⁻¹' B := by
    ext x
    constructor
    · rintro ⟨y, hyB, rfl⟩
      -- We need `e (e.symm y) ∈ B`, but `e (e.symm y) = y`.
      simpa [e.apply_symm_apply] using hyB
    · intro hx
      -- `hx : e x ∈ B`
      exact ⟨e x, hx, by simpa using (e.symm_apply_apply x)⟩
  -- 3. Prove `P1 (e ⁻¹' B)`.
  intro x hx_pre
  -- View `x` as an element of `e.symm '' B`.
  have hx_image : x ∈ (e.symm '' B : Set X) := by
    exact ⟨e x, hx_pre, by simpa using (e.symm_apply_apply x)⟩
  -- Apply `P1` for that set.
  have hx_cl : x ∈ closure (interior (e.symm '' B)) := hImage hx_image
  -- Rewrite everything using the set equality.
  simpa [h_eq] using hx_cl

theorem P2_prod_symm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : Topology.P2 (A ×ˢ B) → Topology.P2 (B ×ˢ A) := by
  intro hP2
  -- Transport `P2` along the coordinate‐swap homeomorphism.
  have hImage : Topology.P2
      ((Homeomorph.prodComm X Y) '' (A ×ˢ B) : Set (Y × X)) :=
    P2_image_homeomorph (e := Homeomorph.prodComm X Y) (A := A ×ˢ B) hP2
  -- The image of `A ×ˢ B` under the swap is `B ×ˢ A`.
  have hImage_eq :
      ((Homeomorph.prodComm X Y) '' (A ×ˢ B) : Set (Y × X)) = B ×ˢ A := by
    ext p
    constructor
    · rintro ⟨q, ⟨hqA, hqB⟩, rfl⟩
      exact ⟨hqB, hqA⟩
    · rintro ⟨hpB, hpA⟩
      refine ⟨(p.2, p.1), ?_, ?_⟩
      · exact ⟨hpA, hpB⟩
      · simp
  simpa [hImage_eq] using hImage

theorem P2_of_P3_and_closed {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → Topology.P3 A → Topology.P2 A := by
  intro hClosed hP3
  have hP1 : Topology.P1 A := P1_closed_of_P3 (A := A) hClosed hP3
  exact Topology.P2_of_P1_and_P3 (A := A) hP1 hP3

theorem P3_of_P1_and_open {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → Topology.P1 A → Topology.P3 A := by
  intro hA_open hP1
  exact ((P1_iff_P3_of_open (A := A) hA_open)).1 hP1

theorem P1_prod_comm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : Topology.P1 (A ×ˢ B) ↔ Topology.P1 (B ×ˢ A) := by
  -- Define the coordinate swap homeomorphism.
  let e := Homeomorph.prodComm X Y
  -- Image of `A ×ˢ B` under `e`.
  have hImage_eq :
      (e '' (A ×ˢ B) : Set (Y × X)) = B ×ˢ A := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases hq with ⟨hqA, hqB⟩
      exact ⟨hqB, hqA⟩
    · rintro ⟨hpB, hpA⟩
      refine ⟨(p.2, p.1), ?_, ?_⟩
      · exact ⟨hpA, hpB⟩
      · simp [e]
  -- Image of `B ×ˢ A` under `e.symm`.
  have hImage_eq_symm :
      (e.symm '' (B ×ˢ A) : Set (X × Y)) = A ×ˢ B := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      rcases hp with ⟨hpB, hpA⟩
      exact ⟨hpA, hpB⟩
    · rintro ⟨hqA, hqB⟩
      refine ⟨(q.2, q.1), ?_, ?_⟩
      · exact ⟨hqB, hqA⟩
      · simp [e]
  -- Equivalence of the two `P1` properties.
  constructor
  · intro hP1
    have h := P1_image_homeomorph (e := e) (A := A ×ˢ B) hP1
    simpa [hImage_eq] using h
  · intro hP1'
    have h := P1_image_homeomorph (e := e.symm) (A := B ×ˢ A) hP1'
    simpa [hImage_eq_symm] using h

theorem P3_prod_swap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : Topology.P3 (A ×ˢ B) ↔ Topology.P3 (B ×ˢ A) := by
  -- Define the coordinate swap homeomorphism.
  let e := Homeomorph.prodComm X Y
  -- The image of `A ×ˢ B` under `e` is `B ×ˢ A`.
  have hImageAB :
      (e '' (A ×ˢ B) : Set (Y × X)) = B ×ˢ A := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases hq with ⟨hqA, hqB⟩
      exact ⟨hqB, hqA⟩
    · rintro ⟨hpB, hpA⟩
      refine ⟨(p.2, p.1), ?_, ?_⟩
      · exact ⟨hpA, hpB⟩
      · simp [e]
  -- Conversely, the image of `B ×ˢ A` under `e.symm` is `A ×ˢ B`.
  have hImageBA :
      (e.symm '' (B ×ˢ A) : Set (X × Y)) = A ×ˢ B := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      rcases hp with ⟨hpB, hpA⟩
      exact ⟨hpA, hpB⟩
    · rintro ⟨hqA, hqB⟩
      refine ⟨(q.2, q.1), ?_, ?_⟩
      · exact ⟨hqB, hqA⟩
      · simp [e]
  -- Assemble the equivalence using `P3_image_homeomorph`.
  constructor
  · intro hP3
    have h := P3_image_homeomorph (e := e) (A := (A ×ˢ B)) hP3
    simpa [hImageAB] using h
  · intro hP3
    have h := P3_image_homeomorph (e := e.symm) (A := (B ×ˢ A)) hP3
    simpa [hImageBA] using h

theorem P1_of_discrete {X : Type*} [TopologicalSpace X] [DiscreteTopology X] {A : Set X} : Topology.P1 A := by
  intro x hxA
  have h_int : interior (A : Set X) = A := (isOpen_discrete _).interior_eq
  have hx_cl : x ∈ closure (A : Set X) := subset_closure hxA
  simpa [h_int] using hx_cl

theorem P2_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] : Topology.P2 ((Set.univ : Set X) ×ˢ (Set.univ : Set Y)) := by
  intro x hx
  simpa [interior_univ, closure_univ] using (Set.mem_univ (x : X × Y))

theorem P3_union_sUnion {X : Type*} [TopologicalSpace X] {𝓢 : Set (Set X)} {B : Set X} : (∀ A ∈ 𝓢, Topology.P3 A) → Topology.P3 B → Topology.P3 (B ∪ ⋃₀ 𝓢) := by
  intro hP3S hP3B
  have hP3_sUnion : Topology.P3 (⋃₀ 𝓢) := by
    apply P3_sUnion (X := X) (𝓢 := 𝓢)
    exact hP3S
  exact P3_union (A := B) (B := ⋃₀ 𝓢) hP3B hP3_sUnion

theorem P3_of_closed_complement {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed (Aᶜ)) : Topology.P3 A := by
  have hOpen : IsOpen (A : Set X) := by
    simpa using hA.isOpen_compl
  exact P3_of_open (A := A) hOpen

theorem P1_prod_univ_left {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : Topology.P1 A → Topology.P1 (A ×ˢ (Set.univ : Set Y)) := by
  intro hP1A
  -- `univ` in `Y` trivially satisfies `P1`.
  have hP1_univ : P1 (Set.univ : Set Y) := by
    simpa using (P1_univ (X := Y))
  -- Apply the product lemma.
  simpa using
    (P1_prod (A := A) (B := (Set.univ : Set Y)) hP1A hP1_univ)

theorem P3_preimage_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} (hB : IsOpen B) (f : C(X, Y)) : P3 (f ⁻¹' B) := by
  have hOpenPre : IsOpen (f ⁻¹' B) := by
    simpa using hB.preimage f.continuous
  exact P3_of_open (A := f ⁻¹' B) hOpenPre

theorem P1_sdiff_of_closed {X : Type*} [TopologicalSpace X] {A B : Set X} : IsClosed B → Topology.P1 A → Topology.P1 (A \ B) := by
  intro hClosedB hP1A
  intro x hxAB
  -- Decompose the hypothesis `x ∈ A \ B`.
  have hxA : x ∈ A := hxAB.1
  have hxNotB : x ∉ B := hxAB.2
  -- From `P1 A`, we know `x ∈ closure (interior A)`.
  have hx_cl : x ∈ closure (interior A) := hP1A hxA
  -- We will use the neighbourhood characterisation of `closure`.
  have h_intA :
      ∀ U : Set X, IsOpen U → x ∈ U → (U ∩ interior A).Nonempty :=
    (mem_closure_iff).1 hx_cl
  -- Goal: every neighbourhood of `x` meets `interior (A \ B)`.
  have h_goal :
      ∀ U : Set X, IsOpen U → x ∈ U → (U ∩ interior (A \ B)).Nonempty := by
    intro U hU hxU
    -- Work inside the open set `U ∩ Bᶜ`.
    have hOpen_comp : IsOpen (Bᶜ) := hClosedB.isOpen_compl
    have hV_open : IsOpen (U ∩ Bᶜ) := hU.inter hOpen_comp
    have hxV : x ∈ U ∩ Bᶜ := by
      exact ⟨hxU, by
        -- `x ∈ Bᶜ` since `x ∉ B`.
        simpa using hxNotB⟩
    -- Apply the closure property of `interior A`.
    have h_nonempty := h_intA (U ∩ Bᶜ) hV_open hxV
    rcases h_nonempty with ⟨z, ⟨hzU, hzBcomp⟩, hzIntA⟩
    -- Show that `z ∈ interior (A \ B)`.
    have hzIntAB : (z : X) ∈ interior (A \ B) := by
      -- `interior A` and `Bᶜ` are open.
      have hOpen_intA : IsOpen (interior A) := isOpen_interior
      have hOpen_int : IsOpen (interior A ∩ Bᶜ) :=
        hOpen_intA.inter hOpen_comp
      -- `z` lies in this open set.
      have hz_mem : z ∈ interior A ∩ Bᶜ := ⟨hzIntA, hzBcomp⟩
      -- This open set is contained in `A \ B`.
      have h_subset :
          (interior A ∩ Bᶜ : Set X) ⊆ A \ B := by
        intro w hw
        exact ⟨interior_subset hw.1, hw.2⟩
      -- Use the neighbourhood criterion for `interior`.
      have h_nhds :
          (interior A ∩ Bᶜ : Set X) ∈ 𝓝 z :=
        hOpen_int.mem_nhds hz_mem
      have h_nhds' : (A \ B : Set X) ∈ 𝓝 z :=
        Filter.mem_of_superset h_nhds h_subset
      exact (mem_interior_iff_mem_nhds).2 h_nhds'
    -- `z` witnesses the required non‐emptiness.
    exact ⟨z, ⟨hzU, hzIntAB⟩⟩
  -- Apply the neighbourhood characterisation to conclude.
  exact (mem_closure_iff).2 h_goal

theorem P2_of_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X} (h : interior A = A) : P2 A := by
  have hA_open : IsOpen (A : Set X) := by
    simpa [h] using (isOpen_interior : IsOpen (interior A))
  simpa using (P2_of_open (A := A) hA_open)

theorem P3_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} : Topology.P3 B → Topology.P3 (e ⁻¹' B) := by
  intro hP3B
  -- 1. Transport `P3 B` along the inverse homeomorphism.
  have hImage : Topology.P3 (e.symm '' B) := by
    simpa using (P3_image_homeomorph (e := e.symm) (A := B) hP3B)
  -- 2. Identify `e.symm '' B` with the preimage `e ⁻¹' B`.
  have h_eq : (e.symm '' B : Set X) = e ⁻¹' B := by
    ext x
    constructor
    · rintro ⟨y, hyB, rfl⟩
      simpa using hyB
    · intro hx
      exact ⟨e x, hx, by simpa using e.symm_apply_apply x⟩
  -- 3. Use `hImage` to obtain the desired inclusion.
  intro x hx
  -- Regard `x` as an element of `e.symm '' B`.
  have hx_image : x ∈ (e.symm '' B : Set X) :=
    ⟨e x, hx, by simpa using e.symm_apply_apply x⟩
  -- Apply `P3` for that set.
  have hx_int : x ∈ interior (closure (e.symm '' B)) := hImage hx_image
  -- Rewrite using the identified sets.
  simpa [h_eq] using hx_int

theorem P2_of_discrete {X : Type*} [TopologicalSpace X] [DiscreteTopology X] {A : Set X} : Topology.P2 A := by
  simpa using (P2_of_open (A := A) (isOpen_discrete _))

theorem P3_prod_univ_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : Topology.P3 A → Topology.P3 (A ×ˢ (Set.univ : Set Y)) := by
  intro hP3A
  -- `univ` in `Y` trivially satisfies `P3`.
  have hP3_univ : Topology.P3 (Set.univ : Set Y) := by
    simpa using (Topology.P3_univ (X := Y))
  -- Apply the product lemma.
  simpa using
    (Topology.P3_prod (A := A) (B := (Set.univ : Set Y)) hP3A hP3_univ)

theorem P2_compl_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → P2 (Aᶜ) := by
  intro hClosedA
  have hOpen : IsOpen (Aᶜ : Set X) := hClosedA.isOpen_compl
  have hP3 : P3 (Aᶜ : Set X) := P3_compl_of_closed (A := A) hClosedA
  exact (P3_iff_P2_of_open (A := Aᶜ) hOpen).1 hP3

theorem P2_union_open {X : Type*} [TopologicalSpace X] {A B : Set X} (hB : IsOpen B) : P2 A → P2 (A ∪ B) := by
  intro hP2A
  have hP2B : P2 B := P2_of_open (A := B) hB
  exact P2_union (A := A) (B := B) hP2A hP2B

theorem P3_closed_iff_open {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → (Topology.P3 A ↔ IsOpen A) := by
  intro hClosed
  have h_closure_eq : closure (A : Set X) = A := hClosed.closure_eq
  constructor
  · intro hP3
    -- First, show `A ⊆ interior A`.
    have h_subset : (A : Set X) ⊆ interior A := by
      intro x hx
      have hx' : x ∈ interior (closure (A : Set X)) := hP3 hx
      simpa [h_closure_eq] using hx'
    -- Hence `interior A = A`.
    have h_int_eq : interior (A : Set X) = A := by
      apply le_antisymm
      · exact interior_subset
      · exact h_subset
    -- Therefore `A` is open.
    have hIsOpen : IsOpen A := by
      simpa [h_int_eq] using
        (isOpen_interior : IsOpen (interior (A : Set X)))
    exact hIsOpen
  · intro hOpen
    exact P3_of_open (A := A) hOpen

theorem exists_dense_P2_subset_univ {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ A : Set X, P2 A ∧ closure A = Set.univ := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · simpa using (P2_univ (X := X))
  · simp [closure_univ]

theorem P1_sigma_family {ι X : Type*} [TopologicalSpace ι] [TopologicalSpace X] {A : ι → Set X} : (∀ i, P1 (A i)) → P1 {p : Σ i, X | p.2 ∈ A p.1} := by
  intro hP1
  -- Define the total set once and for all.
  let S : Set (Σ i : ι, X) := {p | p.2 ∈ A p.1}
  intro p hp
  -- Decompose the point `p`.
  rcases p with ⟨i, x⟩
  -- Translate `hp`.
  have hxA : x ∈ A i := by
    simpa [S] using hp
  ------------------------------------------------------------------
  -- Goal:  `⟨i , x⟩ ∈ closure (interior S)`.
  ------------------------------------------------------------------
  have : (⟨i, x⟩ : Σ i, X) ∈ closure (interior S) := by
    -- Use the neighbourhood-closure criterion.
    refine (mem_closure_iff).2 ?_
    intro U hUopen hxU
    --------------------------------------------------------------
    -- Slice the neighbourhood `U` along the fixed index `i`.
    --------------------------------------------------------------
    let V : Set X := {y | (⟨i, y⟩ : Σ i, X) ∈ U}
    have hVopen : IsOpen V := by
      -- `U` is an open subset of a `Σ`-type, hence each slice is open.
      have hSlices := (isOpen_sigma_iff).1 hUopen
      simpa [V] using hSlices i
    have hxV : x ∈ V := by
      -- Because `⟨i , x⟩ ∈ U`.
      simpa [V] using hxU
    --------------------------------------------------------------
    -- Apply `P1` in the fibre to reach the interior of `A i`.
    --------------------------------------------------------------
    have hx_cl : x ∈ closure (interior (A i)) := (hP1 i) hxA
    -- Therefore `V ∩ interior (A i)` is non-empty.
    have h_nonempty : (V ∩ interior (A i)).Nonempty := by
      have hmem := (mem_closure_iff).1 hx_cl
      exact hmem V hVopen hxV
    rcases h_nonempty with ⟨y, hyV, hyIntA⟩
    --------------------------------------------------------------
    -- Build a point in `U ∩ interior S`.
    --------------------------------------------------------------
    let q : Σ i, X := ⟨i, y⟩
    have hqU : (q : Σ i, X) ∈ U := by
      simpa [V, q] using hyV
    -- Auxiliary open set living inside `S`.
    let T : Set (Σ i, X) := {p : Σ i, X | p.2 ∈ interior (A p.1)}
    have hTopen : IsOpen T := by
      refine (isOpen_sigma_iff).2 ?_
      intro j
      simpa [T] using (isOpen_interior : IsOpen (interior (A j)))
    have hqT : (q : Σ i, X) ∈ T := by
      dsimp [T, q] at *
      exact hyIntA
    -- `T ⊆ S`.
    have hTsub : (T : Set (Σ i, X)) ⊆ S := by
      intro r hr
      dsimp [T, S] at hr ⊢
      exact interior_subset hr
    -- Hence `q` lies in the interior of `S`.
    have hqIntS : (q : Σ i, X) ∈ interior S := by
      have h_nhds : (T : Set (Σ i, X)) ∈ 𝓝 q := hTopen.mem_nhds hqT
      have h_nhds' : (S : Set (Σ i, X)) ∈ 𝓝 q :=
        Filter.mem_of_superset h_nhds hTsub
      exact (mem_interior_iff_mem_nhds).2 h_nhds'
    -- Provide the witness required by the closure criterion.
    exact ⟨q, hqU, hqIntS⟩
  -- Re-express `S`.
  simpa [S] using this