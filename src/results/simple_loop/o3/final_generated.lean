import Mathlib
import Aesop

namespace Topology

variable {X : Type*} [TopologicalSpace X]

/-- A set is semi-open if it is a subset of the closure of its interior. -/
def SemiOpen (A : Set X) : Prop :=
  A ⊆ closure (interior A)

/-- A set is alpha-open if it is a subset of the interior of the closure of its interior. -/
def AlphaOpen (A : Set X) : Prop :=
  A ⊆ interior (closure (interior A))

/-- A set is preopen if it is a subset of the interior of its closure. -/
def PreOpen (A : Set X) : Prop :=
  A ⊆ interior (closure A)


theorem AlphaOpen.to_SemiOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : AlphaOpen A) : SemiOpen A := by
  unfold AlphaOpen SemiOpen at *
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := hA hx
  have hsubset : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  exact hsubset hx'

theorem SemiOpen.union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : SemiOpen A) (hB : SemiOpen B) : SemiOpen (A ∪ B) := by
  unfold SemiOpen at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hxA' : x ∈ closure (interior A) := hA hxA
      have h_sub : interior A ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      exact (closure_mono h_sub) hxA'
  | inr hxB =>
      have hxB' : x ∈ closure (interior B) := hB hxB
      have h_sub : interior B ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      exact (closure_mono h_sub) hxB'

namespace Topology

theorem AlphaOpen.union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : AlphaOpen A) (hB : AlphaOpen B) : AlphaOpen (A ∪ B) := by
  unfold AlphaOpen at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hxA' : x ∈ interior (closure (interior A)) := hA hxA
      have hInt : interior A ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      have hCl : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hInt
      have hInt' : interior (closure (interior A)) ⊆
          interior (closure (interior (A ∪ B))) :=
        interior_mono hCl
      exact hInt' hxA'
  | inr hxB =>
      have hxB' : x ∈ interior (closure (interior B)) := hB hxB
      have hInt : interior B ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      have hCl : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hInt
      have hInt' : interior (closure (interior B)) ⊆
          interior (closure (interior (A ∪ B))) :=
        interior_mono hCl
      exact hInt' hxB'

end Topology

theorem PreOpen.union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : PreOpen A) (hB : PreOpen B) : PreOpen (A ∪ B) := by
  unfold PreOpen at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hxA' : x ∈ interior (closure A) := hA hxA
      have h_cl : closure A ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      have h_int : interior (closure A) ⊆ interior (closure (A ∪ B)) :=
        interior_mono h_cl
      exact h_int hxA'
  | inr hxB =>
      have hxB' : x ∈ interior (closure B) := hB hxB
      have h_cl : closure B ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      have h_int : interior (closure B) ⊆ interior (closure (A ∪ B)) :=
        interior_mono h_cl
      exact h_int hxB'

namespace Topology

theorem AlphaOpen.empty {X : Type*} [TopologicalSpace X] :
    AlphaOpen (∅ : Set X) := by
  unfold AlphaOpen
  intro x hx
  cases hx

end Topology

theorem Topology.SemiOpen.empty {X : Type*} [TopologicalSpace X] :
    Topology.SemiOpen (∅ : Set X) := by
  unfold Topology.SemiOpen
  intro x hx
  cases hx

theorem SemiOpen_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.SemiOpen (interior A) := by
  unfold Topology.SemiOpen
  intro x hx
  have h_cl : x ∈ closure (interior A) := subset_closure hx
  simpa [interior_interior] using h_cl

theorem Topology.AlphaOpen.to_PreOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.AlphaOpen A) : Topology.PreOpen A := by
  unfold Topology.AlphaOpen Topology.PreOpen at *
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := hA hx
  have h_closure_subset : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : interior A ⊆ A)
  have h_interior_subset :
      interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono h_closure_subset
  exact h_interior_subset hx'

theorem AlphaOpen_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.AlphaOpen (interior A) := by
  unfold Topology.AlphaOpen
  intro x hx
  have h_subset : interior (interior A) ⊆ interior (closure (interior A)) :=
    interior_mono (subset_closure : interior A ⊆ closure (interior A))
  have hx' : x ∈ interior (interior A) := by
    simpa [interior_interior] using hx
  have hx'' : x ∈ interior (closure (interior A)) := h_subset hx'
  simpa [interior_interior] using hx''

theorem PreOpen_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.PreOpen (interior A) := by
  unfold Topology.PreOpen
  intro x hx
  have h_subset : interior (interior A) ⊆ interior (closure (interior A)) := by
    apply interior_mono
    exact (subset_closure : (interior A : Set X) ⊆ closure (interior A))
  have hx' : x ∈ interior (interior A) := by
    simpa [interior_interior] using hx
  exact h_subset hx'

theorem Topology.PreOpen.empty {X : Type*} [TopologicalSpace X] :
    Topology.PreOpen (∅ : Set X) := by
  unfold Topology.PreOpen
  intro x hx
  cases hx

theorem Topology.AlphaOpen_interior_of_SemiOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : Topology.SemiOpen A) :
    Topology.AlphaOpen (interior A) := by
  intro x hx
  have h₁ : interior A ⊆ closure (interior A) :=
    calc
      interior A ⊆ A := interior_subset
      _ ⊆ closure (interior A) := hA
  have h₂ : interior (interior A) ⊆ interior (closure (interior A)) :=
    interior_mono h₁
  have hx' : x ∈ interior (interior A) := by
    simpa [interior_interior] using hx
  have : x ∈ interior (closure (interior A)) := h₂ hx'
  simpa [interior_interior] using this

theorem IsOpen.to_PreOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.PreOpen (A : Set X) := by
  unfold Topology.PreOpen
  intro x hx
  have hInt : interior A = A := hA.interior_eq
  have hx_int : x ∈ interior A := by
    simpa [hInt] using hx
  have h_subset : interior A ⊆ interior (closure A) :=
    interior_mono (subset_closure : A ⊆ closure A)
  exact h_subset hx_int

theorem IsOpen.to_AlphaOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.AlphaOpen (A : Set X) := by
  -- First, obtain that an open set is preopen
  have hPre : Topology.PreOpen (A : Set X) := IsOpen.to_PreOpen hA
  -- Unfold the relevant definitions
  unfold Topology.AlphaOpen at *
  unfold Topology.PreOpen at hPre
  intro x hx
  -- From preopenness, `x` lies in `interior (closure A)`
  have hx' : x ∈ interior (closure A) := hPre hx
  -- Since `A` is open, `interior A = A`, so the two closures coincide
  have h_cl : closure (interior A) = closure A := by
    simpa [hA.interior_eq] using rfl
  -- Conclude the desired membership
  simpa [h_cl] using hx'

theorem IsOpen.to_SemiOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.SemiOpen (A : Set X) := by
  unfold Topology.SemiOpen
  intro x hx
  have hxInt : x ∈ interior A := by
    simpa [hA.interior_eq] using hx
  exact subset_closure hxInt

namespace Topology

theorem PreOpen.iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X}
    (hA : ∀ i, PreOpen (A i)) : PreOpen (⋃ i, A i) := by
  unfold PreOpen at *
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have hx_int : x ∈ interior (closure (A i)) := (hA i) hx_i
  have h_subset : closure (A i) ⊆ closure (⋃ j, A j) := by
    apply closure_mono
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  have h_int_subset :
      interior (closure (A i)) ⊆ interior (closure (⋃ j, A j)) :=
    interior_mono h_subset
  exact h_int_subset hx_int

end Topology

namespace Topology

theorem AlphaOpen.iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X}
    (hA : ∀ i, AlphaOpen (A i)) : AlphaOpen (⋃ i, A i) := by
  unfold AlphaOpen at *
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have hx_i' : x ∈ interior (closure (interior (A i))) := (hA i) hx_i
  have hInt : interior (A i) ⊆ interior (⋃ j, A j) := by
    apply interior_mono
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  have hCl : closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) :=
    closure_mono hInt
  have hIntCl :
      interior (closure (interior (A i))) ⊆
        interior (closure (interior (⋃ j, A j))) :=
    interior_mono hCl
  exact hIntCl hx_i'

end Topology

theorem SemiOpen.iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X}
    (hA : ∀ i, Topology.SemiOpen (A i)) : Topology.SemiOpen (⋃ i, A i) := by
  unfold Topology.SemiOpen at *
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have hx_cl : x ∈ closure (interior (A i)) := (hA i) hx_i
  have h_subset : interior (A i) ⊆ interior (⋃ j, A j) := by
    apply interior_mono
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  have h_closure_subset :
      closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) :=
    closure_mono h_subset
  exact h_closure_subset hx_cl

theorem SemiOpen_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.SemiOpen (interior (closure A)) := by
  unfold Topology.SemiOpen
  intro x hx
  have h_cl : x ∈ closure (interior (closure A)) := subset_closure hx
  simpa [interior_interior] using h_cl

theorem PreOpen_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.PreOpen (interior (closure A)) := by
  have hOpen : IsOpen (interior (closure A)) := isOpen_interior
  simpa using (IsOpen.to_PreOpen hOpen)

theorem Topology.PreOpen.univ {X : Type*} [TopologicalSpace X] :
    Topology.PreOpen (Set.univ : Set X) := by
  unfold Topology.PreOpen
  intro x hx
  simpa [closure_univ, interior_univ] using hx

theorem SemiOpen_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.SemiOpen (closure (interior A)) := by
  unfold Topology.SemiOpen
  intro x hx
  -- `interior A` is contained in its own closure, hence (by `interior_mono`)
  -- contained in the interior of that closure
  have h_int_subset : interior A ⊆ interior (closure (interior A)) := by
    have : interior (interior A) ⊆ interior (closure (interior A)) := by
      apply interior_mono
      exact (subset_closure : interior A ⊆ closure (interior A))
    simpa [interior_interior] using this
  -- Taking closures preserves inclusions
  have h_closure_subset :
      closure (interior A) ⊆ closure (interior (closure (interior A))) :=
    closure_mono h_int_subset
  exact h_closure_subset hx

theorem Topology.AlphaOpen.univ {X : Type*} [TopologicalSpace X] :
    Topology.AlphaOpen (Set.univ : Set X) := by
  unfold Topology.AlphaOpen
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem Topology.SemiOpen.univ {X : Type*} [TopologicalSpace X] :
    Topology.SemiOpen (Set.univ : Set X) := by
  unfold Topology.SemiOpen
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem IsClosed.compl_PreOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : Topology.PreOpen (Aᶜ) := by
  have hOpen : IsOpen (Aᶜ) := hA.isOpen_compl
  simpa using (IsOpen.to_PreOpen hOpen)

theorem closure_diff_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A \ B) ⊆ closure A := by
  exact closure_mono (Set.diff_subset : (A \ B : Set X) ⊆ A)

namespace Topology

theorem PreOpen.sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ S, S ∈ 𝒜 → PreOpen S) :
    PreOpen (⋃₀ 𝒜) := by
  unfold PreOpen at *
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨S, hS𝒜, hxS⟩
  have hx_int : x ∈ interior (closure S) := (h𝒜 S hS𝒜) hxS
  have h_subset : closure S ⊆ closure (⋃₀ 𝒜) := by
    apply closure_mono
    intro y hy
    exact Set.mem_sUnion.2 ⟨S, hS𝒜, hy⟩
  have h_int_subset :
      interior (closure S) ⊆ interior (closure (⋃₀ 𝒜)) :=
    interior_mono h_subset
  exact h_int_subset hx_int

end Topology

theorem Topology.PreOpen.exists_open_superset_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : Topology.PreOpen A) :
    ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ U ⊆ closure A := by
  refine ⟨interior (closure A), isOpen_interior, ?_, interior_subset⟩
  intro x hx
  exact hA hx

theorem Topology.AlphaOpen.sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ S, S ∈ 𝒜 → Topology.AlphaOpen S) :
    Topology.AlphaOpen (⋃₀ 𝒜) := by
  unfold Topology.AlphaOpen at *
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨S, hS𝒜, hxS⟩
  have hxInt : x ∈ interior (closure (interior S)) := (h𝒜 S hS𝒜) hxS
  have h_subset : interior (closure (interior S)) ⊆
      interior (closure (interior (⋃₀ 𝒜))) := by
    -- `S` is contained in `⋃₀ 𝒜`
    have hSsubset : (S : Set X) ⊆ ⋃₀ 𝒜 := by
      intro y hy
      exact Set.mem_sUnion.2 ⟨S, hS𝒜, hy⟩
    -- Therefore `interior S` is contained in `interior (⋃₀ 𝒜)`
    have hIntSubset : interior S ⊆ interior (⋃₀ 𝒜) :=
      interior_mono hSsubset
    -- Taking closures preserves inclusions
    have hClSubset : closure (interior S) ⊆ closure (interior (⋃₀ 𝒜)) :=
      closure_mono hIntSubset
    -- Likewise for interiors
    exact interior_mono hClSubset
  exact h_subset hxInt

theorem Topology.AlphaOpen.exists_open_superset_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.AlphaOpen A) :
    ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ U ⊆ closure (interior A) := by
  refine ⟨interior (closure (interior A)), isOpen_interior, ?_, interior_subset⟩
  intro x hx
  exact hA hx

theorem AlphaOpen_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.AlphaOpen (interior (closure A)) := by
  have hOpen : IsOpen (interior (closure A)) := isOpen_interior
  simpa using (IsOpen.to_AlphaOpen hOpen)

theorem Topology.SemiOpen.sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ S, S ∈ 𝒜 → Topology.SemiOpen S) :
    Topology.SemiOpen (⋃₀ 𝒜) := by
  unfold Topology.SemiOpen at *
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨S, hS𝒜, hxS⟩
  have hx_cl : x ∈ closure (interior S) := (h𝒜 S hS𝒜) hxS
  have hSsubset : (S : Set X) ⊆ ⋃₀ 𝒜 := by
    intro y hy
    exact Set.mem_sUnion.2 ⟨S, hS𝒜, hy⟩
  have hInt_subset : interior S ⊆ interior (⋃₀ 𝒜) :=
    interior_mono hSsubset
  have hCl_subset : closure (interior S) ⊆ closure (interior (⋃₀ 𝒜)) :=
    closure_mono hInt_subset
  exact hCl_subset hx_cl

theorem AlphaOpen_interior_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.AlphaOpen (interior (closure (interior A))) := by
  have hOpen : IsOpen (interior (closure (interior A))) := isOpen_interior
  simpa using (IsOpen.to_AlphaOpen hOpen)

theorem IsClosed.preopen_iff_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.PreOpen (A : Set X) ↔ IsOpen (A : Set X) := by
  constructor
  · intro hPre
    -- Since `A` is closed, its closure is itself.
    have h_closure : closure A = A := hA.closure_eq
    -- From `PreOpen`, we have `A ⊆ interior (closure A) = interior A`.
    have h_subset : A ⊆ interior (closure A) := hPre
    have h_subset' : A ⊆ interior A := by
      simpa [h_closure] using h_subset
    -- The interior is always contained in the set.
    have h_int_subset : interior A ⊆ A := interior_subset
    -- Hence `interior A = A`.
    have h_eq : interior A = A :=
      Set.Subset.antisymm h_int_subset h_subset'
    -- The interior is open, so `A` is open.
    have : IsOpen (interior A) := isOpen_interior
    simpa [h_eq] using this
  · intro hOpen
    exact IsOpen.to_PreOpen hOpen

theorem IsClosed.compl_AlphaOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) : Topology.AlphaOpen (Aᶜ : Set X) := by
  have hOpen : IsOpen (Aᶜ : Set X) := hA.isOpen_compl
  simpa using IsOpen.to_AlphaOpen hOpen

theorem Topology.SemiOpen.exists_open_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : Topology.SemiOpen A) :
    ∃ U : Set X, IsOpen U ∧ U ⊆ A ∧ A ⊆ closure U := by
  refine ⟨interior A, isOpen_interior, interior_subset, ?_⟩
  intro x hx
  have : x ∈ closure (interior A) := hA hx
  simpa using this

theorem Topology.PreOpen_iff_exists_open_superset_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.PreOpen A ↔ ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ U ⊆ closure A := by
  constructor
  · intro hA
    exact Topology.PreOpen.exists_open_superset_subset_closure hA
  · rintro ⟨U, hUopen, hAU, hUsubset⟩
    unfold Topology.PreOpen
    intro x hxA
    have hxU : x ∈ U := hAU hxA
    have hUsubsetInterior : U ⊆ interior (closure A) := by
      have hInt : interior U ⊆ interior (closure A) := by
        have hIncl : (U : Set X) ⊆ closure A := hUsubset
        exact interior_mono hIncl
      simpa [hUopen.interior_eq] using hInt
    exact hUsubsetInterior hxU

theorem IsClosed.compl_SemiOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) : Topology.SemiOpen (Aᶜ : Set X) := by
  have hOpen : IsOpen (Aᶜ : Set X) := hA.isOpen_compl
  simpa using IsOpen.to_SemiOpen hOpen

theorem Topology.SemiOpen.closure_subset {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.SemiOpen A) : closure A ⊆ closure (interior A) := by
  have : closure A ⊆ closure (closure (interior A)) := closure_mono hA
  simpa [closure_closure] using this

theorem Topology.SemiOpen_iff_exists_open_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.SemiOpen A ↔ ∃ U : Set X, IsOpen U ∧ U ⊆ A ∧ A ⊆ closure U := by
  constructor
  · intro hA
    exact Topology.SemiOpen.exists_open_subset_closure hA
  · rintro ⟨U, hUopen, hUsubsetA, hAsubset⟩
    unfold Topology.SemiOpen
    intro x hxA
    have hx_closureU : x ∈ closure U := hAsubset hxA
    have hU_subset_intA : (U : Set X) ⊆ interior A := by
      have hInt : interior U ⊆ interior A := interior_mono hUsubsetA
      simpa [hUopen.interior_eq] using hInt
    have h_closure_subset : closure U ⊆ closure (interior A) :=
      closure_mono hU_subset_intA
    exact h_closure_subset hx_closureU

theorem IsClosed.alphaOpen_iff_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.AlphaOpen (A : Set X) ↔ IsOpen (A : Set X) := by
  constructor
  · intro hAlpha
    -- `hAlpha` gives the inclusion `A ⊆ interior (closure (interior A))`
    have hSubset₁ : (A : Set X) ⊆ interior (closure (interior A)) := hAlpha
    -- Since `A` is closed, `closure (interior A) ⊆ A`
    have hClosureSubset : closure (interior A) ⊆ A := by
      have : closure (interior A) ⊆ closure (A : Set X) :=
        closure_mono (interior_subset : interior A ⊆ A)
      simpa [hA.closure_eq] using this
    -- Hence `interior (closure (interior A)) ⊆ A`
    have hSubset₂ : interior (closure (interior A)) ⊆ A := by
      intro x hx
      have hx' : x ∈ interior A := (interior_mono hClosureSubset) hx
      exact interior_subset hx'
    -- We now have equality of the two sets
    have hEq : interior (closure (interior A)) = (A : Set X) :=
      Set.Subset.antisymm hSubset₂ hSubset₁
    -- The interior of any set is open
    have hOpenInt : IsOpen (interior (closure (interior A))) := isOpen_interior
    simpa [hEq] using hOpenInt
  · intro hOpen
    exact IsOpen.to_AlphaOpen hOpen

theorem Topology.SemiOpen.closure_eq_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : Topology.SemiOpen A) :
    closure A = closure (interior A) := by
  have h₁ : closure A ⊆ closure (interior A) :=
    Topology.SemiOpen.closure_subset hA
  have h₂ : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : (interior A : Set X) ⊆ A)
  exact Set.Subset.antisymm h₁ h₂

theorem IsOpen.preopen_iff_alphaopen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.PreOpen (A : Set X) ↔ Topology.AlphaOpen (A : Set X) := by
  -- Basic equalities for an open set `A`
  have hInt : interior (A : Set X) = A := hA.interior_eq
  have hClEq : closure (interior (A : Set X)) = closure (A : Set X) := by
    simpa [hInt]
  have hIntClEq :
      interior (closure (interior (A : Set X))) =
        interior (closure (A : Set X)) := by
    simpa [hClEq]
  -- Now show the desired equivalence
  constructor
  · intro hPre
    -- Use the definition of `PreOpen`
    intro x hxA
    have : x ∈ interior (closure (A : Set X)) := hPre hxA
    simpa [hIntClEq] using this
  · intro hAlpha
    -- Use the definition of `AlphaOpen`
    intro x hxA
    have : x ∈ interior (closure (interior (A : Set X))) := hAlpha hxA
    simpa [hIntClEq] using this

namespace Topology

theorem AlphaOpen_iff_exists_open_superset_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    AlphaOpen A ↔ ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ U ⊆ closure (interior A) := by
  constructor
  · intro hA
    exact AlphaOpen.exists_open_superset_subset_closure_interior hA
  · rintro ⟨U, hUopen, hAU, hUsubset⟩
    unfold AlphaOpen
    intro x hxA
    -- `x` lies in the chosen open set `U`
    have hxU : x ∈ U := hAU hxA
    -- `U` is a neighbourhood of `x`
    have hU_nhds : U ∈ 𝓝 x := hUopen.mem_nhds hxU
    -- Hence `closure (interior A)` is also a neighbourhood of `x`
    have h_nhds : closure (interior A) ∈ 𝓝 x :=
      Filter.mem_of_superset hU_nhds hUsubset
    -- Translate the neighbourhood statement into membership of the interior
    exact (mem_interior_iff_mem_nhds).2 h_nhds

end Topology

theorem PreOpen_interior_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.PreOpen (interior (closure (interior A))) := by
  have hOpen : IsOpen (interior (closure (interior A))) := isOpen_interior
  simpa using (IsOpen.to_PreOpen hOpen)

namespace Topology

theorem SemiOpen_iff_closure_subset {X : Type*} [TopologicalSpace X] {A : Set X} :
    SemiOpen (A : Set X) ↔ closure A ⊆ closure (interior A) := by
  constructor
  · intro hA
    exact SemiOpen.closure_subset hA
  · intro hClosure
    unfold SemiOpen
    intro x hx
    have hx_closure : x ∈ closure (A : Set X) := subset_closure hx
    exact hClosure hx_closure

end Topology

theorem SemiOpen_interior_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.SemiOpen (interior (closure (interior A))) := by
  unfold Topology.SemiOpen
  intro x hx
  -- Any set is contained in the closure of itself.
  have : x ∈ closure (interior (closure (interior A))) := subset_closure hx
  simpa [interior_interior] using this

theorem Topology.PreOpen.inter_open {X : Type*} [TopologicalSpace X] {A U : Set X}
    (hA : Topology.PreOpen A) (hU : IsOpen U) :
    Topology.PreOpen (A ∩ U) := by
  unfold Topology.PreOpen at *
  intro x hx
  -- `x` lies in both `A` and `U`
  have hxA : x ∈ A := hx.1
  have hxU : x ∈ U := hx.2
  -- From `PreOpen`, obtain that `x` is in the interior of `closure A`
  have hxIntA : x ∈ interior (closure A) := hA hxA
  -- The auxiliary open set `V = interior (closure A) ∩ U`
  have hVopen : IsOpen (interior (closure A) ∩ U) :=
    isOpen_interior.inter hU
  have hxV : x ∈ interior (closure A) ∩ U := by
    exact ⟨hxIntA, hxU⟩
  -- Show that `V ⊆ closure (A ∩ U)`
  have hVsubset : (interior (closure A) ∩ U) ⊆ closure (A ∩ U) := by
    intro y hy
    have hyInt : y ∈ interior (closure A) := hy.1
    have hyU  : y ∈ U := hy.2
    have hy_closureA : y ∈ closure A := interior_subset hyInt
    -- Establish `y ∈ closure (A ∩ U)`
    have : y ∈ closure (A ∩ U) := by
      -- Use the neighbourhood characterization of closure
      apply (mem_closure_iff).2
      intro S hSopen hyS
      -- `S ∩ U` is an open neighbourhood of `y`
      have hSUopen : IsOpen (S ∩ U) := hSopen.inter hU
      have hySU : y ∈ S ∩ U := by
        exact ⟨hyS, hyU⟩
      -- Since `y ∈ closure A`, this neighbourhood meets `A`
      have hNonempty : ((S ∩ U) ∩ A).Nonempty := by
        have hmem :=
          (mem_closure_iff).1 hy_closureA (S ∩ U) hSUopen hySU
        simpa [Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using hmem
      -- Rearrange the intersection to fit the required shape
      simpa [Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using hNonempty
    exact this
  -- `V` is an open neighbourhood of `x` contained in `closure (A ∩ U)`,
  -- hence `x` lies in the interior of `closure (A ∩ U)`
  have hxIntAU : x ∈ interior (closure (A ∩ U)) := by
    have hNhds : (interior (closure A) ∩ U) ∈ 𝓝 x :=
      hVopen.mem_nhds hxV
    have hNhds' : closure (A ∩ U) ∈ 𝓝 x :=
      Filter.mem_of_superset hNhds hVsubset
    exact (mem_interior_iff_mem_nhds).2 hNhds'
  exact hxIntAU

theorem Topology.interior_closure_interior_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (A : Set X))) ⊆ interior (closure A) := by
  have h : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : interior A ⊆ A)
  exact interior_mono h

theorem IsClosed.semiOpen_iff_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.SemiOpen (A : Set X) ↔ closure (interior (A : Set X)) = A := by
  -- First, record that the closure of a closed set is the set itself.
  have h_cl : closure (A : Set X) = A := hA.closure_eq
  -- Establish the desired equivalence.
  constructor
  · -- From `SemiOpen` to equality of closures.
    intro hSemi
    -- One inclusion is immediate from `SemiOpen`.
    have h₁ : (A : Set X) ⊆ closure (interior A) := hSemi
    -- The reverse inclusion follows from monotonicity of `closure`.
    have h₂ : closure (interior (A : Set X)) ⊆ A := by
      have : closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
        closure_mono (interior_subset : interior (A : Set X) ⊆ A)
      simpa [h_cl] using this
    -- Conclude the equality of the two sets.
    exact Set.Subset.antisymm h₂ h₁
  · -- From the equality to `SemiOpen`.
    intro hEq
    -- The required inclusion follows by rewriting with the given equality.
    have hIncl : (A : Set X) ⊆ closure (interior A) := by
      intro x hx
      simpa [hEq] using hx
    -- Unfold the definition of `SemiOpen` to finish.
    simpa [Topology.SemiOpen] using hIncl

namespace Topology

theorem SemiOpen.interior_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : SemiOpen (A : Set X)) :
    interior (closure (A : Set X)) =
      interior (closure (interior (A : Set X))) := by
  -- From `SemiOpen`, we already have equality of the two closures.
  have hCl : closure (A : Set X) = closure (interior (A : Set X)) :=
    SemiOpen.closure_eq_closure_interior hA
  -- Apply `interior` to both sides of that equality.
  simpa using congrArg (fun S : Set X => interior S) hCl

end Topology

theorem Topology.SemiOpen.inter_open {X : Type*} [TopologicalSpace X] {A U : Set X}
    (hA : Topology.SemiOpen A) (hU : IsOpen U) :
    Topology.SemiOpen (A ∩ U) := by
  unfold Topology.SemiOpen at *
  intro x hx
  -- `x` lies in both `A` and `U`.
  have hxA : x ∈ A := hx.1
  have hxU : x ∈ U := hx.2
  -- From `SemiOpen`, obtain `x ∈ closure (interior A)`.
  have hx_clA : x ∈ closure (interior A) := hA hxA
  -- Show that `x ∈ closure (interior A ∩ U)`.
  have hx_clAU : x ∈ closure (interior A ∩ U) := by
    -- Use the neighbourhood characterisation of closure.
    apply (mem_closure_iff).2
    intro V hVopen hxV
    -- `V ∩ U` is an open neighbourhood of `x`.
    have hVUopen : IsOpen (V ∩ U) := hVopen.inter hU
    have hxVU : x ∈ V ∩ U := ⟨hxV, hxU⟩
    -- Since `x ∈ closure (interior A)`, this neighbourhood meets `interior A`.
    have hNonempty : ((V ∩ U) ∩ interior A).Nonempty :=
      (mem_closure_iff).1 hx_clA (V ∩ U) hVUopen hxVU
    -- Rearrange the intersection for the required shape.
    simpa [Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using hNonempty
  -- `interior A ∩ U` is contained in `interior (A ∩ U)`.
  have h_subset : (interior A ∩ U) ⊆ interior (A ∩ U) := by
    intro y hy
    have hyIntA : y ∈ interior A := hy.1
    have hyU : y ∈ U := hy.2
    -- `interior A ∩ U` is an open neighbourhood of `y` contained in `A ∩ U`.
    have hOpen : IsOpen (interior A ∩ U) := isOpen_interior.inter hU
    have hSub : (interior A ∩ U) ⊆ A ∩ U := by
      intro z hz
      exact ⟨interior_subset hz.1, hz.2⟩
    have hNhds : (interior A ∩ U) ∈ 𝓝 y := hOpen.mem_nhds ⟨hyIntA, hyU⟩
    have : A ∩ U ∈ 𝓝 y := Filter.mem_of_superset hNhds hSub
    exact (mem_interior_iff_mem_nhds).2 this
  -- Taking closures preserves inclusions.
  have h_closure_subset :
      closure (interior A ∩ U) ⊆ closure (interior (A ∩ U)) :=
    closure_mono h_subset
  -- Conclude the desired membership.
  exact h_closure_subset hx_clAU

theorem Topology.SemiOpen.interior_preopen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : Topology.SemiOpen A) :
    Topology.PreOpen (interior A) := by
  unfold Topology.PreOpen
  intro x hx
  -- `interior A` is an open neighbourhood of `x`.
  have hOpen : IsOpen (interior A) := isOpen_interior
  have hNhds : interior A ∈ 𝓝 x := hOpen.mem_nhds hx
  -- Since `interior A ⊆ closure (interior A)`, the closure is also a neighbourhood of `x`.
  have hSubset : (interior A : Set X) ⊆ closure (interior A) := subset_closure
  have hNhds' : closure (interior A) ∈ 𝓝 x :=
    Filter.mem_of_superset hNhds hSubset
  -- Therefore `x` lies in the interior of `closure (interior A)`.
  exact (mem_interior_iff_mem_nhds).2 hNhds'

namespace Topology

theorem AlphaOpen.inter_open {X : Type*} [TopologicalSpace X] {A U : Set X}
    (hA : AlphaOpen A) (hU : IsOpen U) :
    AlphaOpen (A ∩ U) := by
  -- Unfold the definition of `AlphaOpen`
  unfold AlphaOpen at *
  intro x hx
  -- Decompose the assumption `x ∈ A ∩ U`
  have hxA : x ∈ A := hx.1
  have hxU : x ∈ U := hx.2
  -- From `AlphaOpen A`, obtain
  have hxIntA : x ∈ interior (closure (interior A)) := hA hxA
  -- Auxiliary open neighbourhood
  have hVopen : IsOpen (interior (closure (interior A)) ∩ U) :=
    isOpen_interior.inter hU
  have hxV : x ∈ interior (closure (interior A)) ∩ U := ⟨hxIntA, hxU⟩
  -- Show the neighbourhood is contained in the required closure
  have hVsubset :
      (interior (closure (interior A)) ∩ U) ⊆
        closure (interior (A ∩ U)) := by
    intro y hy
    have hyIntA : y ∈ interior (closure (interior A)) := hy.1
    have hyU : y ∈ U := hy.2
    have hyClA : y ∈ closure (interior A) := interior_subset hyIntA
    -- Prove `y ∈ closure (interior (A ∩ U))` via neighbourhood criterion
    have : y ∈ closure (interior (A ∩ U)) := by
      apply (mem_closure_iff).2
      intro S hSopen hyS
      -- Consider the open neighbourhood `S ∩ U` of `y`
      have hSUopen : IsOpen (S ∩ U) := hSopen.inter hU
      have hySU : y ∈ S ∩ U := ⟨hyS, hyU⟩
      -- Since `y ∈ closure (interior A)`, we meet `interior A`
      have hNonempty : ((S ∩ U) ∩ interior A).Nonempty :=
        (mem_closure_iff).1 hyClA (S ∩ U) hSUopen hySU
      rcases hNonempty with ⟨z, hzSU, hzIntA⟩
      have hzS : z ∈ S := hzSU.1
      have hzU : z ∈ U := hzSU.2
      -- Relate to `interior (A ∩ U)`
      have hIntEq : interior (A ∩ U) = interior A ∩ U := by
        simpa [hU.interior_eq] using (interior_inter (A := A) (B := U))
      have hzIntAU : z ∈ interior (A ∩ U) := by
        have : z ∈ interior A ∩ U := ⟨hzIntA, hzU⟩
        simpa [hIntEq] using this
      exact ⟨z, ⟨hzS, hzIntAU⟩⟩
    exact this
  -- `x` has an open neighbourhood contained in `closure (interior (A ∩ U))`
  have hxInt : x ∈ interior (closure (interior (A ∩ U))) := by
    have hNhds : (interior (closure (interior A)) ∩ U) ∈ 𝓝 x :=
      hVopen.mem_nhds hxV
    have hNhds' : closure (interior (A ∩ U)) ∈ 𝓝 x :=
      Filter.mem_of_superset hNhds hVsubset
    exact (mem_interior_iff_mem_nhds).2 hNhds'
  exact hxInt

end Topology

theorem Topology.AlphaOpen.closure_subset {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.AlphaOpen (A : Set X)) :
    closure A ⊆ closure (interior A) := by
  -- An α-open set is semi-open.
  have hSemi : Topology.SemiOpen (A : Set X) := AlphaOpen.to_SemiOpen hA
  -- Apply the corresponding lemma for semi-open sets.
  exact Topology.SemiOpen.closure_subset hSemi

theorem IsClosed.preopen_iff_alphaopen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.PreOpen (A : Set X) ↔ Topology.AlphaOpen (A : Set X) := by
  simpa using
    (IsClosed.preopen_iff_open (A := A) hA).trans
      ((IsClosed.alphaOpen_iff_open (A := A) hA).symm)

theorem Topology.AlphaOpen.closure_eq_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : Topology.AlphaOpen (A : Set X)) :
    closure (A : Set X) = closure (interior (A : Set X)) := by
  have hSemi : Topology.SemiOpen (A : Set X) := Topology.AlphaOpen.to_SemiOpen hA
  exact Topology.SemiOpen.closure_eq_closure_interior hSemi

theorem Topology.SemiOpen.union_open {X : Type*} [TopologicalSpace X] {A U : Set X}
    (hA : Topology.SemiOpen A) (hU : IsOpen U) :
    Topology.SemiOpen (A ∪ U) := by
  -- Convert the open set `U` into a semi-open set.
  have hUSemi : Topology.SemiOpen (U : Set X) := IsOpen.to_SemiOpen hU
  -- Apply the union lemma for two semi-open sets.
  simpa using (SemiOpen.union (A := A) (B := U) hA hUSemi)

theorem Topology.AlphaOpen.interior_closure_eq {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : Topology.AlphaOpen (A : Set X)) :
    interior (closure (A : Set X)) =
      interior (closure (interior (A : Set X))) := by
  -- An α-open set is semi-open, so we can use the corresponding lemma.
  have hSemi : Topology.SemiOpen (A : Set X) :=
    Topology.AlphaOpen.to_SemiOpen hA
  simpa using Topology.SemiOpen.interior_closure_eq hSemi

theorem interior_closure_diff_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (A \ B : Set X)) ⊆ interior (closure (A : Set X)) := by
  exact interior_mono (closure_diff_subset (A := A) (B := B))

theorem interior_closure_inter_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (A ∩ B : Set X)) ⊆
      interior (closure A) ∩ interior (closure B) := by
  -- First inclusion: via monotonicity `A ∩ B ⊆ A`.
  have h_left :
      interior (closure (A ∩ B : Set X)) ⊆ interior (closure A) :=
    interior_mono
      (closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A))
  -- Second inclusion: via monotonicity `A ∩ B ⊆ B`.
  have h_right :
      interior (closure (A ∩ B : Set X)) ⊆ interior (closure B) :=
    interior_mono
      (closure_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B))
  -- Combine the two inclusions.
  intro x hx
  exact ⟨h_left hx, h_right hx⟩



theorem closure_inter_interior_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior (A ∩ B : Set X)) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  have h_left : closure (interior (A ∩ B : Set X)) ⊆ closure (interior A) := by
    have hsubset : interior (A ∩ B : Set X) ⊆ interior A :=
      interior_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)
    exact closure_mono hsubset
  have h_right : closure (interior (A ∩ B : Set X)) ⊆ closure (interior B) := by
    have hsubset : interior (A ∩ B : Set X) ⊆ interior B :=
      interior_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)
    exact closure_mono hsubset
  exact ⟨h_left hx, h_right hx⟩

theorem closure_interior_diff_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A \ B : Set X)) ⊆ closure (interior (A : Set X)) := by
  -- First note that `A \ B ⊆ A`.
  have h_subset : (A \ B : Set X) ⊆ A := Set.diff_subset
  -- Taking interiors preserves inclusions.
  have h_int_subset : interior (A \ B : Set X) ⊆ interior (A : Set X) :=
    interior_mono h_subset
  -- Taking closures preserves inclusions as well.
  exact closure_mono h_int_subset

theorem interior_closure_union_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (A : Set X)) ∪ interior (closure (B : Set X)) ⊆
      interior (closure (A ∪ B : Set X)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `closure A ⊆ closure (A ∪ B)`
      have h_cl : closure (A : Set X) ⊆ closure (A ∪ B : Set X) :=
        closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      -- Hence the interiors satisfy the same inclusion
      have h_int : interior (closure (A : Set X)) ⊆
          interior (closure (A ∪ B : Set X)) := interior_mono h_cl
      exact h_int hxA
  | inr hxB =>
      -- `closure B ⊆ closure (A ∪ B)`
      have h_cl : closure (B : Set X) ⊆ closure (A ∪ B : Set X) :=
        closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      -- Hence the interiors satisfy the same inclusion
      have h_int : interior (closure (B : Set X)) ⊆
          interior (closure (A ∪ B : Set X)) := interior_mono h_cl
      exact h_int hxB

namespace Topology

theorem interior_closure_inter_subset_interior_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A : Set X)) ∩ interior (closure (B : Set X)) ⊆
      interior (closure (A ∪ B : Set X)) := by
  intro x hx
  -- `x` lies in both interiors
  have hxA : x ∈ interior (closure (A : Set X)) := hx.1
  have hxB : x ∈ interior (closure (B : Set X)) := hx.2
  -- Define the auxiliary open neighbourhood `V`.
  let V : Set X :=
    interior (closure (A : Set X)) ∩ interior (closure (B : Set X))
  have hVopen : IsOpen V :=
    (isOpen_interior).inter (isOpen_interior)
  have hxV : x ∈ V := by
    dsimp [V]
    exact ⟨hxA, hxB⟩
  -- Show that `V ⊆ closure (A ∪ B)`.
  have hVsubset : (V : Set X) ⊆ closure (A ∪ B : Set X) := by
    intro y hy
    dsimp [V] at hy
    -- From membership in the first factor we get `y ∈ closure A`.
    have hy_clA : y ∈ closure (A : Set X) := interior_subset hy.1
    -- Since `A ⊆ A ∪ B`, the corresponding closures satisfy the same inclusion.
    have h_clA_subset : closure (A : Set X) ⊆ closure (A ∪ B : Set X) :=
      closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
    exact h_clA_subset hy_clA
  -- `V` is an open neighbourhood of `x` contained in `closure (A ∪ B)`,
  -- hence `x` lies in the interior of that set.
  have h_nhds : closure (A ∪ B : Set X) ∈ 𝓝 x :=
    Filter.mem_of_superset (hVopen.mem_nhds hxV) hVsubset
  exact (mem_interior_iff_mem_nhds).2 h_nhds

end Topology

namespace Topology

theorem PreOpen.union_open {X : Type*} [TopologicalSpace X] {A U : Set X}
    (hA : PreOpen (A : Set X)) (hU : IsOpen U) :
    PreOpen (A ∪ U) := by
  have hUpre : PreOpen (U : Set X) := IsOpen.to_PreOpen hU
  simpa using (PreOpen.union (A := A) (B := U) hA hUpre)

end Topology

theorem interior_subset_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior A ⊆ interior (closure A) := by
  exact interior_mono (subset_closure : (A : Set X) ⊆ closure A)

namespace Topology

theorem AlphaOpen.union_open {X : Type*} [TopologicalSpace X] {A U : Set X}
    (hA : AlphaOpen (A : Set X)) (hU : IsOpen U) :
    AlphaOpen (A ∪ U) := by
  -- Turn the open set `U` into an α-open set.
  have hUα : AlphaOpen (U : Set X) := IsOpen.to_AlphaOpen hU
  -- Use the union lemma for two α-open sets.
  simpa using (AlphaOpen.union (A := A) (B := U) hA hUα)

end Topology

theorem interior_union_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    interior (A ∪ B : Set X) = A ∪ B := by
  simpa using (hA.union hB).interior_eq

theorem IsOpen.closure_SemiOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.SemiOpen (closure (A : Set X)) := by
  unfold Topology.SemiOpen
  intro x hx
  -- First, show `A ⊆ interior (closure A)`.
  have hA_subset : (A : Set X) ⊆ interior (closure (A : Set X)) := by
    intro y hyA
    -- `A` is an open neighbourhood of `y`.
    have hA_nhds : (A : Set X) ∈ 𝓝 y := hA.mem_nhds hyA
    -- Since `A ⊆ closure A`, the closure is also a neighbourhood of `y`.
    have hCl_nhds : closure (A : Set X) ∈ 𝓝 y :=
      Filter.mem_of_superset hA_nhds (subset_closure : (A : Set X) ⊆ closure A)
    -- Hence `y ∈ interior (closure A)`.
    exact (mem_interior_iff_mem_nhds).2 hCl_nhds
  -- Taking closures preserves inclusions.
  have hClosure_subset :
      (closure (A : Set X)) ⊆ closure (interior (closure (A : Set X))) :=
    closure_mono hA_subset
  exact hClosure_subset hx

namespace Topology

theorem interior_closure_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (closure (A : Set X))) =
      interior (closure (A : Set X)) := by
  simpa [closure_closure]

end Topology

theorem Topology.AlphaOpen.interior_preopen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.AlphaOpen A) : Topology.PreOpen (interior A) := by
  have hSemi : Topology.SemiOpen (A : Set X) := Topology.AlphaOpen.to_SemiOpen hA
  simpa using Topology.SemiOpen.interior_preopen hSemi

theorem Topology.closure_interior_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    closure (interior (A : Set X)) ⊆ closure (interior (B : Set X)) := by
  exact closure_mono (interior_mono hAB)

namespace Topology

theorem PreOpen.diff_closed {X : Type*} [TopologicalSpace X] {A C : Set X}
    (hA : PreOpen (A : Set X)) (hC : IsClosed (C : Set X)) :
    PreOpen (A \ C) := by
  -- The complement of a closed set is open.
  have hOpenCompl : IsOpen ((C : Set X)ᶜ) := hC.isOpen_compl
  -- Rewrite the set difference as an intersection with this open complement
  -- and apply the intersection lemma for preopen sets.
  simpa [Set.diff_eq, Set.inter_comm] using
    (PreOpen.inter_open (A := A) (U := Cᶜ) hA hOpenCompl)

end Topology

theorem Topology.SemiOpen.diff_closed {X : Type*} [TopologicalSpace X] {A C : Set X}
    (hA : Topology.SemiOpen (A : Set X)) (hC : IsClosed (C : Set X)) :
    Topology.SemiOpen (A \ C) := by
  -- The complement of a closed set is open.
  have hOpenCompl : IsOpen ((C : Set X)ᶜ) := hC.isOpen_compl
  -- Rewrite the set difference as an intersection with this open complement
  -- and apply the intersection lemma for semi-open sets.
  simpa [Set.diff_eq, Set.inter_comm] using
    (Topology.SemiOpen.inter_open (A := A) (U := Cᶜ) hA hOpenCompl)

namespace Topology

theorem PreOpen.closure_SemiOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : PreOpen (A : Set X)) :
    SemiOpen (closure (A : Set X)) := by
  -- Unfold the definition of `SemiOpen`.
  unfold SemiOpen
  intro x hxCl
  -- We show that `x ∈ closure (interior (closure A))` using the
  -- neighbourhood characterisation of the closure.
  apply (mem_closure_iff).2
  intro U hUopen hxU
  -- Since `x ∈ closure A`, the neighbourhood `U` meets `A`.
  have hNonempty : ((U ∩ A).Nonempty) :=
    (mem_closure_iff).1 hxCl U hUopen hxU
  rcases hNonempty with ⟨y, hyU, hyA⟩
  -- As `A` is preopen, the point `y` lies in `interior (closure A)`.
  have hyInt : y ∈ interior (closure (A : Set X)) := hA hyA
  -- Hence `y` witnesses that `U` meets `interior (closure A)`.
  exact ⟨y, ⟨hyU, hyInt⟩⟩

end Topology

theorem isOpen_interior_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsOpen (interior (closure (interior (A : Set X)))) := by
  simpa using isOpen_interior

namespace Topology

theorem AlphaOpen.closure_SemiOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : AlphaOpen (A : Set X)) :
    SemiOpen (closure (A : Set X)) := by
  -- An α-open set is preopen.
  have hPre : PreOpen (A : Set X) := AlphaOpen.to_PreOpen hA
  -- The closure of a preopen set is semi-open.
  exact PreOpen.closure_SemiOpen hPre

end Topology

namespace Topology

theorem AlphaOpen.diff_closed {X : Type*} [TopologicalSpace X] {A C : Set X}
    (hA : AlphaOpen (A : Set X)) (hC : IsClosed (C : Set X)) :
    AlphaOpen (A \ C) := by
  have hOpenCompl : IsOpen (Cᶜ : Set X) := hC.isOpen_compl
  simpa [Set.diff_eq, Set.inter_comm] using
    (AlphaOpen.inter_open (A := A) (U := Cᶜ) hA hOpenCompl)

end Topology

theorem closure_interior_union_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior (A : Set X)) ∪ closure (interior (B : Set X)) ⊆
      closure (interior (A ∪ B : Set X)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `interior A ⊆ interior (A ∪ B)`
      have hInt : interior (A : Set X) ⊆ interior (A ∪ B : Set X) :=
        interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      -- Hence the corresponding closures satisfy the same inclusion
      have hCl :
          closure (interior (A : Set X)) ⊆
            closure (interior (A ∪ B : Set X)) :=
        closure_mono hInt
      exact hCl hxA
  | inr hxB =>
      -- `interior B ⊆ interior (A ∪ B)`
      have hInt : interior (B : Set X) ⊆ interior (A ∪ B : Set X) :=
        interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      -- Hence the corresponding closures satisfy the same inclusion
      have hCl :
          closure (interior (B : Set X)) ⊆
            closure (interior (A ∪ B : Set X)) :=
        closure_mono hInt
      exact hCl hxB

namespace Topology

theorem SemiOpen.closure_SemiOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : SemiOpen (A : Set X)) :
    SemiOpen (closure (A : Set X)) := by
  unfold SemiOpen at *
  intro x hxClA
  -- `SemiOpen` gives equality of the two closures.
  have hEq : (closure (A : Set X)) = closure (interior (A : Set X)) :=
    SemiOpen.closure_eq_closure_interior hA
  -- Transport membership along this equality.
  have hxClIntA : x ∈ closure (interior (A : Set X)) := by
    simpa [hEq] using hxClA
  -- Monotonicity of `closure` applied to 
  -- `interior A ⊆ interior (closure A)`.
  have hSubset :
      closure (interior (A : Set X)) ⊆
        closure (interior (closure (A : Set X))) := by
    have hIntSubset :
        (interior (A : Set X)) ⊆ interior (closure (A : Set X)) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    exact closure_mono hIntSubset
  exact hSubset hxClIntA

end Topology

theorem Topology.closure_subset_of_subset_closure {X : Type*} [TopologicalSpace X]
    {A U : Set X} (h : (U : Set X) ⊆ closure (A : Set X)) :
    closure U ⊆ closure (A : Set X) := by
  have : closure U ⊆ closure (closure (A : Set X)) := closure_mono h
  simpa [closure_closure] using this

theorem SemiOpen_closure_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.SemiOpen (closure (interior (closure A))) := by
  simpa using (SemiOpen_closure_interior (A := closure A))

namespace Topology

theorem SemiOpen_iff_closure_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    SemiOpen (A : Set X) ↔ closure A = closure (interior A) := by
  constructor
  · intro hA
    exact SemiOpen.closure_eq_closure_interior hA
  · intro hEq
    unfold SemiOpen
    intro x hxA
    -- Any point of `A` is in `closure A`.
    have hxClA : x ∈ closure (A : Set X) := subset_closure hxA
    -- Rewrite using the assumed equality of closures.
    simpa [hEq] using hxClA

end Topology



theorem closure_inter_subset_inter_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ B : Set X) ⊆ closure A ∩ closure B := by
  intro x hx
  have hA : closure (A ∩ B : Set X) ⊆ closure A :=
    closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)
  have hB : closure (A ∩ B : Set X) ⊆ closure B :=
    closure_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)
  exact ⟨hA hx, hB hx⟩

theorem interior_subset_interior_union_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A : Set X) ⊆ interior (A ∪ B) := by
  exact interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)

theorem interior_inter_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    interior (A ∩ B : Set X) = A ∩ B := by
  have hOpen : IsOpen (A ∩ B : Set X) := hA.inter hB
  simpa using hOpen.interior_eq

namespace Topology

theorem PreOpen.closure_eq_closure_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : PreOpen (A : Set X)) :
    closure (A : Set X) = closure (interior (closure (A : Set X))) := by
  -- From `PreOpen`, we know that `closure A` is semi-open.
  have hSemi : SemiOpen (closure (A : Set X)) :=
    PreOpen.closure_SemiOpen hA
  -- Apply the characterisation of semi-open sets to `closure A`.
  simpa [closure_closure] using
    SemiOpen.closure_eq_closure_interior hSemi

end Topology

theorem closure_interior_eq_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    closure (interior (A : Set X)) = closure (A : Set X) := by
  simpa [hA.interior_eq]

theorem IsClosed.interior_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    interior (closure (A : Set X)) = interior (A : Set X) := by
  simpa [hA.closure_eq]

namespace Topology

theorem interior_closure_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    interior (closure (A : Set X)) ⊆ interior (closure (B : Set X)) := by
  exact interior_mono (closure_mono hAB)

end Topology

theorem interior_closure_interior_inter_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior (A ∩ B : Set X))) ⊆
      interior (closure (interior A)) ∩
        interior (closure (interior B)) := by
  intro x hx
  -- First inclusion: via `A ∩ B ⊆ A`.
  have h₁ :
      interior (closure (interior (A ∩ B : Set X))) ⊆
        interior (closure (interior A)) := by
    apply interior_mono
    -- `closure` is monotone, so it suffices to prove the inclusion
    -- at the level of the sets being closed.
    have hSubset :
        interior (A ∩ B : Set X) ⊆ interior (A : Set X) :=
      interior_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)
    exact closure_mono hSubset
  -- Second inclusion: via `A ∩ B ⊆ B`.
  have h₂ :
      interior (closure (interior (A ∩ B : Set X))) ⊆
        interior (closure (interior B)) := by
    apply interior_mono
    have hSubset :
        interior (A ∩ B : Set X) ⊆ interior (B : Set X) :=
      interior_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)
    exact closure_mono hSubset
  exact ⟨h₁ hx, h₂ hx⟩

theorem Topology.PreOpen.interior_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.PreOpen (A : Set X)) :
    interior (closure (A : Set X)) =
      interior (closure (interior (closure (A : Set X)))) := by
  -- First, recall the equality of closures for a preopen set.
  have hCl :
      closure (A : Set X) =
        closure (interior (closure (A : Set X))) :=
    Topology.PreOpen.closure_eq_closure_interior_closure (A := A) hA
  -- Apply `interior` to both sides of this equality.
  simpa using congrArg (fun S : Set X => interior S) hCl

namespace Topology

theorem interior_closure_interior_eq_interior_closure_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen (A : Set X)) :
    interior (closure (interior (A : Set X))) =
      interior (closure (A : Set X)) := by
  -- Since `A` is open, we have `interior A = A`.
  have hInt : interior (A : Set X) = A := hA.interior_eq
  -- Rewriting with this equality yields the desired result.
  simpa [hInt]

end Topology





namespace Topology

theorem PreOpen.mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) (hBsubset : (B : Set X) ⊆ interior (closure (A : Set X))) :
    PreOpen (B : Set X) := by
  unfold PreOpen
  intro x hxB
  -- `x` belongs to `interior (closure A)` by assumption.
  have hxIntA : x ∈ interior (closure (A : Set X)) := hBsubset hxB
  -- Since `A ⊆ B`, we have `closure A ⊆ closure B`.
  have hClAB : closure (A : Set X) ⊆ closure (B : Set X) :=
    closure_mono hAB
  -- Taking interiors preserves inclusions.
  have hIntAB :
      interior (closure (A : Set X)) ⊆ interior (closure (B : Set X)) :=
    interior_mono hClAB
  exact hIntAB hxIntA

end Topology

theorem Topology.AlphaOpen.closed_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hA_alpha : Topology.AlphaOpen (A : Set X)) :
    interior (A : Set X) = A := by
  -- A closed α-open set is open, by the characterisation established earlier.
  have hOpen : IsOpen (A : Set X) :=
    (IsClosed.alphaOpen_iff_open (A := A) hA_closed).1 hA_alpha
  -- For an open set, the interior equals the set itself.
  simpa [hOpen.interior_eq]

namespace Topology

variable {X : Type*} [TopologicalSpace X]

theorem interior_closure_interior_mono {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    interior (closure (interior (A : Set X))) ⊆
      interior (closure (interior (B : Set X))) := by
  -- `interior` is monotone
  have h₁ : interior (A : Set X) ⊆ interior (B : Set X) :=
    interior_mono hAB
  -- `closure` is monotone
  have h₂ : closure (interior (A : Set X)) ⊆ closure (interior (B : Set X)) :=
    closure_mono h₁
  -- apply `interior` again
  exact interior_mono h₂

end Topology

namespace Topology

theorem AlphaOpen.of_PreOpen_and_SemiOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hPre : PreOpen (A : Set X)) (hSemi : SemiOpen (A : Set X)) :
    AlphaOpen (A : Set X) := by
  -- Unfold the relevant definitions.
  unfold PreOpen at hPre
  unfold AlphaOpen
  intro x hxA
  -- From `PreOpen`, the point `x` lies in `interior (closure A)`.
  have hxIntCl : x ∈ interior (closure (A : Set X)) := hPre hxA
  -- For a semi-open set, the two closures coincide.
  have hClEq : closure (A : Set X) = closure (interior (A : Set X)) :=
    SemiOpen.closure_eq_closure_interior hSemi
  -- Rewrite the membership using the equality of closures.
  simpa [hClEq] using hxIntCl

end Topology

namespace Topology

theorem AlphaOpen_iff_PreOpen_and_SemiOpen {X : Type*} [TopologicalSpace X] {A : Set X} :
    AlphaOpen (A : Set X) ↔ (PreOpen (A : Set X) ∧ SemiOpen (A : Set X)) := by
  constructor
  · intro hA
    exact ⟨AlphaOpen.to_PreOpen hA, AlphaOpen.to_SemiOpen hA⟩
  · rintro ⟨hPre, hSemi⟩
    exact AlphaOpen.of_PreOpen_and_SemiOpen hPre hSemi

end Topology

theorem Topology.SemiOpen.mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B)
    (hBsubset : (B : Set X) ⊆ closure (interior (A : Set X))) :
    Topology.SemiOpen (B : Set X) := by
  -- Unfold the definition of `SemiOpen`.
  unfold Topology.SemiOpen at *
  intro x hxB
  -- From the hypothesis `hBsubset`, obtain membership in `closure (interior A)`.
  have hxClA : x ∈ closure (interior (A : Set X)) := hBsubset hxB
  -- Since `A ⊆ B`, we have `interior A ⊆ interior B`.
  have hIntSubset : interior (A : Set X) ⊆ interior (B : Set X) :=
    interior_mono hAB
  -- Taking closures preserves inclusions.
  have hClSubset :
      closure (interior (A : Set X)) ⊆ closure (interior (B : Set X)) :=
    closure_mono hIntSubset
  -- Combine the two facts to conclude.
  exact hClSubset hxClA

theorem Topology.AlphaOpen.mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B)
    (hBsubset : (B : Set X) ⊆ interior (closure (interior (A : Set X)))) :
    Topology.AlphaOpen (B : Set X) := by
  unfold Topology.AlphaOpen at *
  intro x hxB
  -- From the hypothesis, `x` lies in `interior (closure (interior A))`.
  have hxIntA : x ∈ interior (closure (interior (A : Set X))) := hBsubset hxB
  -- We now show this interior is contained in `interior (closure (interior B))`.
  have hIntSubset :
      interior (closure (interior (A : Set X))) ⊆
        interior (closure (interior (B : Set X))) := by
    -- `interior` is monotone.
    have h₁ : interior (A : Set X) ⊆ interior (B : Set X) :=
      interior_mono hAB
    -- `closure` is monotone.
    have h₂ : closure (interior (A : Set X)) ⊆ closure (interior (B : Set X)) :=
      closure_mono h₁
    -- Apply `interior` once more.
    exact interior_mono h₂
  exact hIntSubset hxIntA



theorem isClosed_closure_diff_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsClosed (closure (A : Set X) \ interior (closure (A : Set X))) := by
  -- `closure A` is closed.
  have hClosedCl : IsClosed (closure (A : Set X)) := isClosed_closure
  -- The complement of the open set `interior (closure A)` is closed.
  have hClosedCompl :
      IsClosed ((interior (closure (A : Set X)))ᶜ) :=
    (isOpen_interior : IsOpen (interior (closure (A : Set X)))).isClosed_compl
  -- The desired set is the intersection of two closed sets.
  simpa [Set.diff_eq, Set.inter_comm] using hClosedCl.inter hClosedCompl

theorem Topology.PreOpen.exists_open_superset_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.PreOpen A) :
    ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ U ⊆ interior (closure A) := by
  refine ⟨interior (closure A), isOpen_interior, ?_, subset_rfl⟩
  intro x hx
  exact hA hx

namespace Topology

theorem AlphaOpen.closure_eq_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : AlphaOpen (A : Set X)) :
    closure (A : Set X) = closure (interior (closure (A : Set X))) := by
  -- An α-open set is preopen.
  have hPre : PreOpen (A : Set X) := AlphaOpen.to_PreOpen hA
  -- Apply the corresponding lemma for preopen sets.
  simpa using
    PreOpen.closure_eq_closure_interior_closure (A := A) hPre

end Topology

theorem Topology.AlphaOpen.closure_interior_SemiOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : Topology.AlphaOpen (A : Set X)) :
    Topology.SemiOpen (closure (interior (A : Set X))) := by
  -- The set `interior A` is open.
  have hOpen : IsOpen (interior (A : Set X)) := isOpen_interior
  -- The closure of an open set is semi-open.
  simpa using (IsOpen.closure_SemiOpen (A := interior A) hOpen)



namespace Topology

theorem closure_interior_subset_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (A : Set X)) ⊆ closure (A : Set X) := by
  exact closure_mono (interior_subset : interior (A : Set X) ⊆ A)

end Topology

namespace Topology

variable {X : Type*} [TopologicalSpace X]

theorem closure_interior_closure_mono {A B : Set X} (hAB : (A : Set X) ⊆ B) :
    closure (interior (closure (A : Set X))) ⊆
      closure (interior (closure (B : Set X))) := by
  -- Monotonicity of `closure` gives `closure A ⊆ closure B`.
  have h₁ : closure (A : Set X) ⊆ closure (B : Set X) :=
    closure_mono hAB
  -- Applying `interior` preserves inclusions.
  have h₂ : interior (closure (A : Set X)) ⊆ interior (closure (B : Set X)) :=
    interior_mono h₁
  -- Applying `closure` once more yields the desired inclusion.
  exact closure_mono h₂

end Topology

theorem Topology.SemiOpen.union_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : Topology.SemiOpen (A : Set X)) :
    Topology.SemiOpen (A ∪ closure (interior (A : Set X))) := by
  -- `closure (interior A)` is semi-open.
  have hClInt : Topology.SemiOpen (closure (interior (A : Set X))) :=
    SemiOpen_closure_interior (A := A)
  -- The union of two semi-open sets is semi-open.
  simpa using
    (SemiOpen.union (A := A) (B := closure (interior A)) hA hClInt)

namespace Topology

theorem PreOpen_iff_exists_open_superset_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    PreOpen (A : Set X) ↔
      ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ U ⊆ interior (closure (A : Set X)) := by
  constructor
  · intro hA
    exact PreOpen.exists_open_superset_subset_interior_closure (A := A) hA
  · rintro ⟨U, hUopen, hAU, hUsubset⟩
    unfold PreOpen
    intro x hxA
    have hxU : x ∈ U := hAU hxA
    exact hUsubset hxU

end Topology

namespace Topology

variable {X : Type*} [TopologicalSpace X]

theorem PreOpen.closure_subset {A : Set X} (hA : PreOpen (A : Set X)) :
    closure (A : Set X) ⊆ closure (interior (closure (A : Set X))) := by
  -- From `PreOpen`, we have the inclusion `A ⊆ interior (closure A)`.
  have hSubset : (A : Set X) ⊆ interior (closure (A : Set X)) := hA
  -- Taking closures preserves inclusions, yielding the desired result.
  exact closure_mono hSubset

end Topology

theorem interior_inter_subset_inter_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ B : Set X) ⊆ interior A ∩ interior B := by
  intro x hx
  have hA : x ∈ interior (A : Set X) :=
    (interior_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)) hx
  have hB : x ∈ interior (B : Set X) :=
    (interior_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)) hx
  exact ⟨hA, hB⟩

namespace Topology

variable {X : Type*} [TopologicalSpace X]

theorem PreOpen_iff_pointwise
    {A : Set X} :
    PreOpen (A : Set X) ↔
      ∀ x, x ∈ A →
        ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ closure A := by
  constructor
  · intro hA x hxA
    refine ⟨interior (closure A), isOpen_interior, ?_, interior_subset⟩
    exact hA hxA
  · intro hLocal
    unfold PreOpen
    intro x hxA
    rcases hLocal x hxA with ⟨U, hUopen, hxU, hUsubset⟩
    have hU_nhds : U ∈ 𝓝 x := hUopen.mem_nhds hxU
    have hCl_nhds : closure A ∈ 𝓝 x :=
      Filter.mem_of_superset hU_nhds hUsubset
    exact (mem_interior_iff_mem_nhds).2 hCl_nhds

end Topology





theorem interior_diff_closed_eq {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB : IsClosed (B : Set X)) :
    interior (A \ B : Set X) = interior (A : Set X) \ B := by
  ext x
  constructor
  · intro hx
    have hxIntA : x ∈ interior (A : Set X) :=
      (interior_mono (Set.diff_subset : (A \ B : Set X) ⊆ A)) hx
    have hxNotB : x ∉ B := by
      have hxAB : x ∈ A \ B := interior_subset hx
      exact hxAB.2
    exact ⟨hxIntA, hxNotB⟩
  · intro hx
    rcases hx with ⟨hxIntA, hxNotB⟩
    -- The sets `interior A` and `Bᶜ` are open.
    have hOpenIntA : IsOpen (interior (A : Set X)) := isOpen_interior
    have hOpenComplB : IsOpen ((B : Set X)ᶜ) := hB.isOpen_compl
    -- Their intersection is an open neighbourhood of `x`.
    have hOpen : IsOpen (interior A ∩ (B : Set X)ᶜ) :=
      hOpenIntA.inter hOpenComplB
    have hxIn : x ∈ interior A ∩ (B : Set X)ᶜ := by
      exact ⟨hxIntA, hxNotB⟩
    -- This neighbourhood is contained in `A \ B`.
    have hSubset : (interior A ∩ (B : Set X)ᶜ) ⊆ (A \ B : Set X) := by
      intro y hy
      exact ⟨interior_subset hy.1, hy.2⟩
    -- Conclude that `x` lies in the interior of `A \ B`.
    have hNhds : (interior A ∩ (B : Set X)ᶜ) ∈ 𝓝 x :=
      hOpen.mem_nhds hxIn
    exact (mem_interior_iff_mem_nhds).2 (Filter.mem_of_superset hNhds hSubset)

theorem Topology.SemiOpen.preopen_iff_alphaopen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hS : Topology.SemiOpen (A : Set X)) :
    Topology.PreOpen (A : Set X) ↔ Topology.AlphaOpen (A : Set X) := by
  -- Use the general equivalence `AlphaOpen ↔ PreOpen ∧ SemiOpen`.
  have hEquiv := Topology.AlphaOpen_iff_PreOpen_and_SemiOpen (A := A)
  -- Combine this with the given hypothesis `hS`.
  constructor
  · intro hPre
    have : Topology.PreOpen (A : Set X) ∧ Topology.SemiOpen (A : Set X) :=
      ⟨hPre, hS⟩
    exact (hEquiv).mpr this
  · intro hAlpha
    exact Topology.AlphaOpen.to_PreOpen hAlpha

theorem isClosed_closure_diff_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsClosed (closure (A : Set X) \ interior (A : Set X)) := by
  -- `closure A` is closed.
  have hClosedCl : IsClosed (closure (A : Set X)) := isClosed_closure
  -- The complement of the open set `interior A` is closed.
  have hClosedCompl :
      IsClosed ((interior (A : Set X))ᶜ) :=
    (isOpen_interior : IsOpen (interior (A : Set X))).isClosed_compl
  -- The desired set is the intersection of two closed sets.
  simpa [Set.diff_eq, Set.inter_comm] using hClosedCl.inter hClosedCompl

namespace Topology

theorem AlphaOpen.subset_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : AlphaOpen (A : Set X)) :
    (A : Set X) ⊆ interior (closure (A : Set X)) := by
  intro x hxA
  -- From `AlphaOpen`, obtain membership in `interior (closure (interior A))`.
  have hx_int : x ∈ interior (closure (interior (A : Set X))) := hA hxA
  -- `closure (interior A)` is contained in `closure A`.
  have h_closure_subset :
      closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
    closure_mono (interior_subset : interior (A : Set X) ⊆ A)
  -- Taking interiors preserves inclusions.
  have h_interior_subset :
      interior (closure (interior (A : Set X))) ⊆
        interior (closure (A : Set X)) :=
    interior_mono h_closure_subset
  -- Conclude the desired membership.
  exact h_interior_subset hx_int

end Topology



theorem Topology.PreOpen.subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.PreOpen (A : Set X)) :
    (A : Set X) ⊆ interior (closure (A : Set X)) := hA

theorem Topology.PreOpen.subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.PreOpen (A : Set X)) :
    (A : Set X) ⊆ closure (interior (closure (A : Set X))) := by
  intro x hxA
  have hxInt : x ∈ interior (closure (A : Set X)) := hA hxA
  have : x ∈ closure (interior (closure (A : Set X))) :=
    subset_closure hxInt
  exact this

theorem Continuous.preimage_interior_subset_interior_preimage
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : Continuous f) {B : Set Y} :
    f ⁻¹' interior B ⊆ interior (f ⁻¹' B) := by
  intro x hx
  -- Define `U` as the interior of `B`.
  set U : Set Y := interior B with hUdef
  have hUopen : IsOpen U := by
    dsimp [hUdef]
    exact isOpen_interior
  have hUsubset : U ⊆ B := by
    dsimp [hUdef]
    exact interior_subset
  have hfxU : f x ∈ U := by
    simpa [hUdef] using hx
  -- The preimage of `U` is an open neighbourhood of `x`.
  have hVopen : IsOpen (f ⁻¹' U) := hUopen.preimage hf
  have hxV : x ∈ f ⁻¹' U := hfxU
  have hVsubset : (f ⁻¹' U : Set X) ⊆ f ⁻¹' B := by
    intro y hy
    exact hUsubset hy
  -- Conclude that `x` lies in the interior of `f ⁻¹' B`.
  have h_nhds : f ⁻¹' B ∈ 𝓝 x :=
    Filter.mem_of_superset (hVopen.mem_nhds hxV) hVsubset
  exact (mem_interior_iff_mem_nhds).2 h_nhds

namespace Topology

variable {X : Type*} [TopologicalSpace X]

theorem closure_subset_of_subset_interior_closure {A B : Set X}
    (h : (B : Set X) ⊆ interior (closure (A : Set X))) :
    closure (B : Set X) ⊆ closure (A : Set X) := by
  -- First, upgrade the assumption to a subset of `closure A`.
  have h₁ : (B : Set X) ⊆ closure (A : Set X) := by
    intro x hxB
    have : x ∈ interior (closure (A : Set X)) := h hxB
    exact interior_subset this
  -- Apply monotonicity of `closure` and simplify.
  have h₂ : closure (B : Set X) ⊆ closure (closure (A : Set X)) :=
    closure_mono h₁
  simpa [closure_closure] using h₂

end Topology

theorem closure_inter_interior_subset_closure_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A : Set X) ∩ interior (B : Set X) ⊆
      closure (A ∩ B : Set X) := by
  intro x hx
  have hxCl : x ∈ closure (A : Set X) := hx.1
  have hxInt : x ∈ interior (B : Set X) := hx.2
  -- Use the neighbourhood characterization of the closure.
  apply (mem_closure_iff).2
  intro V hVopen hxV
  -- The auxiliary open neighbourhood `V ∩ interior B`.
  have hVIntOpen : IsOpen (V ∩ interior (B : Set X)) :=
    hVopen.inter isOpen_interior
  have hxVInt : x ∈ V ∩ interior (B : Set X) := ⟨hxV, hxInt⟩
  -- Since `x ∈ closure A`, this neighbourhood meets `A`.
  have hNonempty : ((V ∩ interior (B : Set X)) ∩ A).Nonempty :=
    (mem_closure_iff).1 hxCl (V ∩ interior B) hVIntOpen hxVInt
  rcases hNonempty with ⟨y, ⟨⟨hyV, hyIntB⟩, hyA⟩⟩
  -- The point `y` lies in `B` because it is in `interior B`.
  have hyB : y ∈ B := interior_subset hyIntB
  -- Hence `y` witnesses that `V` meets `A ∩ B`.
  exact ⟨y, ⟨hyV, ⟨hyA, hyB⟩⟩⟩

theorem interior_inter_closure_compl_eq_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (A : Set X) ∩ closure ((A : Set X)ᶜ) = (∅ : Set X) := by
  apply Set.eq_empty_iff_forall_not_mem.2
  intro x hx
  have hxInt : x ∈ interior (A : Set X) := hx.1
  have hxCl  : x ∈ closure ((A : Set X)ᶜ) := hx.2
  -- Use the neighbourhood `interior A` of `x` to derive a contradiction.
  have hNonempty :
      ((interior (A : Set X)) ∩ (A : Set X)ᶜ).Nonempty :=
    (mem_closure_iff).1 hxCl (interior A) isOpen_interior hxInt
  rcases hNonempty with ⟨y, hyInt, hyNotA⟩
  have hyA : y ∈ (A : Set X) := interior_subset hyInt
  exact hyNotA hyA

theorem IsClosed.closure_interior_eq_of_SemiOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X))
    (hA_semi : Topology.SemiOpen (A : Set X)) :
    closure (interior (A : Set X)) = A := by
  exact
    (IsClosed.semiOpen_iff_eq_closure_interior (A := A) hA_closed).1 hA_semi



theorem Topology.AlphaOpen_iff_pointwise {X : Type*} [TopologicalSpace X] {A : Set X} :
    AlphaOpen (A : Set X) ↔
      ∀ x, x ∈ A →
        ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ closure (interior (A : Set X)) := by
  constructor
  · intro hA x hxA
    refine ⟨interior (closure (interior (A : Set X))), isOpen_interior, ?_, interior_subset⟩
    exact hA hxA
  · intro hLocal
    unfold AlphaOpen
    intro x hxA
    rcases hLocal x hxA with ⟨U, hUopen, hxU, hUsubset⟩
    -- `U` is an open neighbourhood of `x` contained in `closure (interior A)`.
    have hNhds : (U : Set X) ∈ 𝓝 x := hUopen.mem_nhds hxU
    have hNhds' : closure (interior (A : Set X)) ∈ 𝓝 x :=
      Filter.mem_of_superset hNhds hUsubset
    -- Hence `x` lies in the interior of `closure (interior A)`.
    exact (mem_interior_iff_mem_nhds).2 hNhds'

theorem Topology.SemiOpen.subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : Topology.SemiOpen (A : Set X)) :
    (A : Set X) ⊆ closure (interior (A : Set X)) := by
  intro x hxA
  exact hA hxA

theorem Topology.SemiOpen.inter_closure_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    Topology.SemiOpen (A ∩ closure (interior (A : Set X))) := by
  unfold Topology.SemiOpen
  intro x hx
  -- `x` lies in `closure (interior A)` by virtue of belonging to the intersection.
  have hxCl : x ∈ closure (interior (A : Set X)) := hx.2
  -- We show that `interior A` is contained in the interior of the intersection,
  -- hence their closures satisfy the same inclusion.
  have hSubset :
      interior (A : Set X) ⊆
        interior (A ∩ closure (interior (A : Set X))) := by
    -- `interior A` itself sits inside the intersection.
    have hIncl :
        (interior (A : Set X)) ⊆
          A ∩ closure (interior (A : Set X)) := by
      intro y hy
      exact ⟨interior_subset hy, subset_closure hy⟩
    -- Apply monotonicity of `interior`, recalling `interior (interior A) = interior A`.
    have hInt :
        interior (interior (A : Set X)) ⊆
          interior (A ∩ closure (interior (A : Set X))) :=
      interior_mono hIncl
    simpa [interior_interior] using hInt
  -- Taking closures preserves inclusions.
  have hClosure :
      closure (interior (A : Set X)) ⊆
        closure (interior (A ∩ closure (interior (A : Set X)))) :=
    closure_mono hSubset
  exact hClosure hxCl

theorem Topology.PreOpen.union_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : Topology.PreOpen (A : Set X)) :
    Topology.PreOpen (A ∪ interior (closure (A : Set X))) := by
  -- `interior (closure A)` is preopen by a general lemma.
  have hIntCl : Topology.PreOpen (interior (closure (A : Set X))) :=
    by
      simpa using (PreOpen_interior_closure (A := A))
  -- The union of two preopen sets is preopen.
  simpa using
    (PreOpen.union (A := A) (B := interior (closure A)) hA hIntCl)

namespace Topology

variable {X : Type*} [TopologicalSpace X]

theorem closure_closure_interior (A : Set X) :
    closure (closure (interior (A : Set X))) = closure (interior (A : Set X)) := by
  simpa [closure_closure]

end Topology



namespace Topology

theorem closure_interior_closure_interior_eq_closure_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (A : Set X)))) =
      closure (interior (A : Set X)) := by
  apply Set.Subset.antisymm
  · -- `closure (interior (closure (interior A))) ⊆ closure (interior A)`
    have hsubset :
        interior (closure (interior (A : Set X))) ⊆
          closure (interior (A : Set X)) := by
      intro x hx
      exact interior_subset hx
    have hclosure :
        closure (interior (closure (interior (A : Set X)))) ⊆
          closure (closure (interior (A : Set X))) :=
      closure_mono hsubset
    simpa [closure_closure] using hclosure
  · -- `closure (interior A) ⊆ closure (interior (closure (interior A)))`
    have hsubset :
        interior (A : Set X) ⊆
          interior (closure (interior (A : Set X))) := by
      have :
          interior (interior (A : Set X)) ⊆
            interior (closure (interior (A : Set X))) := by
        apply interior_mono
        exact (subset_closure :
          interior (A : Set X) ⊆ closure (interior (A : Set X)))
      simpa [interior_interior] using this
    have hclosure :
        closure (interior (A : Set X)) ⊆
          closure (interior (closure (interior (A : Set X)))) :=
      closure_mono hsubset
    simpa using hclosure

end Topology

theorem Topology.SemiOpen.union_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : Topology.SemiOpen (A : Set X)) :
    Topology.SemiOpen (A ∪ interior (A : Set X)) := by
  -- `interior A` is semi-open by a general lemma.
  have hInt : Topology.SemiOpen (interior (A : Set X)) :=
    (SemiOpen_interior (A := A))
  -- The union of two semi-open sets is semi-open.
  simpa using
    (SemiOpen.union (A := A) (B := interior A) hA hInt)



namespace Topology

theorem PreOpen.closure_interior_SemiOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : PreOpen (A : Set X)) :
    SemiOpen (closure (interior (A : Set X))) := by
  -- `interior A` is open.
  have hOpen : IsOpen (interior (A : Set X)) := isOpen_interior
  -- The closure of an open set is semi-open.
  simpa using (IsOpen.closure_SemiOpen (A := interior A) hOpen)

end Topology

namespace Topology

theorem AlphaOpen.union_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : AlphaOpen (A : Set X)) :
    AlphaOpen (A ∪ interior (closure (A : Set X))) := by
  -- `interior (closure A)` is an open set.
  have hOpen : IsOpen (interior (closure (A : Set X))) := isOpen_interior
  -- Apply the union lemma for an α-open set with an open set.
  simpa using
    (AlphaOpen.union_open (A := A) (U := interior (closure A)) hA hOpen)

end Topology

theorem Topology.SemiOpen.interior_nonempty_of_nonempty
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.SemiOpen (A : Set X)) (hNE : (A : Set X).Nonempty) :
    (interior (A : Set X)).Nonempty := by
  classical
  by_cases hInt : (interior (A : Set X)).Nonempty
  · exact hInt
  · exfalso
    rcases hNE with ⟨x, hxA⟩
    -- From semi-openness we have `x ∈ closure (interior A)`.
    have hxCl : x ∈ closure (interior (A : Set X)) := hA hxA
    -- Under the assumption `interior A` is empty, its closure is also empty.
    have hIntEq : interior (A : Set X) = (∅ : Set X) := by
      apply Set.eq_empty_iff_forall_not_mem.2
      intro y hy
      exact hInt ⟨y, hy⟩
    have : x ∈ (∅ : Set X) := by
      simpa [hIntEq, closure_empty] using hxCl
    exact this.elim

theorem Topology.PreOpen.exists_closed_superset_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.PreOpen (A : Set X)) :
    ∃ F : Set X, IsClosed F ∧ (A : Set X) ⊆ interior F ∧ F ⊆ closure (A : Set X) := by
  refine ⟨closure (A : Set X), isClosed_closure, ?_, subset_rfl⟩
  intro x hxA
  exact hA hxA

theorem closure_union_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A : Set X) ∪ closure (B : Set X) ⊆ closure (A ∪ B : Set X) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `closure A ⊆ closure (A ∪ B)`
      have h_cl : closure (A : Set X) ⊆ closure (A ∪ B : Set X) :=
        closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      exact h_cl hxA
  | inr hxB =>
      -- `closure B ⊆ closure (A ∪ B)`
      have h_cl : closure (B : Set X) ⊆ closure (A ∪ B : Set X) :=
        closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      exact h_cl hxB



theorem closure_inter_interior_subset_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ interior (B : Set X)) ⊆ closure (B : Set X) := by
  -- The set `A ∩ interior B` is contained in `B`.
  have hSubset : (A ∩ interior (B : Set X) : Set X) ⊆ B := by
    intro x hx
    exact interior_subset hx.2
  -- Monotonicity of `closure` gives the desired inclusion.
  exact closure_mono hSubset

theorem Continuous.preimage_PreOpen
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : Continuous f) {V : Set Y} (hV : IsOpen V) :
    Topology.PreOpen (f ⁻¹' V) := by
  -- The preimage of an open set under a continuous map is open.
  have hOpen : IsOpen (f ⁻¹' V) := hV.preimage hf
  -- Any open set is preopen.
  simpa using (IsOpen.to_PreOpen hOpen)

theorem interior_union_subset_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A : Set X) ∪ interior (B : Set X) ⊆
      interior (A ∪ B : Set X) := by
  intro x hx
  cases hx with
  | inl hA =>
      have h :
          interior (A : Set X) ⊆ interior (A ∪ B : Set X) :=
        interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      exact h hA
  | inr hB =>
      have h :
          interior (B : Set X) ⊆ interior (A ∪ B : Set X) :=
        interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      exact h hB

namespace Topology

variable {X : Type*} [TopologicalSpace X]

theorem AlphaOpen_iff_PreOpen_and_closure_eq_closure_interior {A : Set X} :
    AlphaOpen (A : Set X) ↔
      (PreOpen (A : Set X) ∧ closure (A : Set X) = closure (interior (A : Set X))) := by
  -- We already know `AlphaOpen A ↔ PreOpen A ∧ SemiOpen A`.
  have h₁ := AlphaOpen_iff_PreOpen_and_SemiOpen (A := A)
  -- And `SemiOpen A ↔ closure A = closure (interior A)`.
  have h₂ := SemiOpen_iff_closure_eq_closure_interior (A := A)
  -- Prove the two implications.
  constructor
  · intro hAlpha
    -- Obtain `PreOpen A` and `SemiOpen A`.
    rcases (h₁).1 hAlpha with ⟨hPre, hSemi⟩
    -- Turn `SemiOpen A` into the desired equality of closures.
    have hEq : closure (A : Set X) = closure (interior (A : Set X)) :=
      (SemiOpen.closure_eq_closure_interior hSemi)
    exact ⟨hPre, hEq⟩
  · rintro ⟨hPre, hEq⟩
    -- Convert the closure equality back into `SemiOpen A`.
    have hSemi : SemiOpen (A : Set X) := (h₂).2 hEq
    -- Combine to get `AlphaOpen A`.
    exact (h₁).2 ⟨hPre, hSemi⟩

end Topology



theorem Topology.PreOpen.interior_closure_nonempty_of_nonempty
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.PreOpen (A : Set X)) (hNE : (A : Set X).Nonempty) :
    (interior (closure (A : Set X))).Nonempty := by
  rcases hNE with ⟨x, hxA⟩
  exact ⟨x, hA hxA⟩

namespace Topology

variable {X : Type*} [TopologicalSpace X]

theorem AlphaOpen.union_interior {A : Set X} (hA : AlphaOpen (A : Set X)) :
    AlphaOpen (A ∪ interior (A : Set X)) := by
  -- `interior A` is an open set.
  have hOpen : IsOpen (interior (A : Set X)) := isOpen_interior
  -- Apply the general union lemma with an open set.
  simpa using
    (AlphaOpen.union_open (A := A) (U := interior A) hA hOpen)

end Topology

theorem interior_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    interior (A ∪ B : Set X) = A ∪ B := by
  simpa using (hA.union hB).interior_eq

namespace Topology

theorem AlphaOpen.nonempty_iff_interior_nonempty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : AlphaOpen (A : Set X)) :
    (A : Set X).Nonempty ↔ (interior (A : Set X)).Nonempty := by
  -- An α-open set is semi-open.
  have hSemi : SemiOpen (A : Set X) := AlphaOpen.to_SemiOpen hA
  constructor
  · -- From non-emptiness of `A`, deduce non-emptiness of its interior.
    intro hNE
    exact SemiOpen.interior_nonempty_of_nonempty hSemi hNE
  · -- The interior is contained in the set, so non-emptiness lifts.
    intro hIntNE
    rcases hIntNE with ⟨x, hxInt⟩
    exact ⟨x, interior_subset hxInt⟩

end Topology

theorem Topology.SemiOpen.nonempty_iff_interior_nonempty
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.SemiOpen (A : Set X)) :
    (A : Set X).Nonempty ↔ (interior (A : Set X)).Nonempty := by
  constructor
  · intro hANonempty
    exact Topology.SemiOpen.interior_nonempty_of_nonempty hA hANonempty
  · intro hIntNonempty
    rcases hIntNonempty with ⟨x, hxInt⟩
    exact ⟨x, interior_subset hxInt⟩

theorem closure_inter_interior_subset_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X) ∩ B) ⊆ closure (A : Set X) := by
  -- The set `interior A ∩ B` is contained in `A`.
  have hSubset : (interior (A : Set X) ∩ B : Set X) ⊆ A := by
    intro x hx
    exact interior_subset hx.1
  -- Monotonicity of `closure` gives the desired inclusion.
  exact closure_mono hSubset

theorem AlphaOpen_interior_closure_interior_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    Topology.AlphaOpen (interior (closure (interior (closure A)))) := by
  have hOpen :
      IsOpen (interior (closure (interior (closure A)))) :=
    isOpen_interior
  simpa using (IsOpen.to_AlphaOpen hOpen)

theorem Set.Subset.eq_empty_iff {α : Type*} {s : Set α} :
    (s : Set α) = (∅ : Set α) ↔ ∀ x, x ∉ s := by
  constructor
  · intro h
    simpa [h]
  · intro h
    exact (Set.eq_empty_iff_forall_not_mem).2 h

theorem interior_closure_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) ⊆ closure (A : Set X) := by
  intro x hx
  exact interior_subset hx

namespace Topology

theorem PreOpen.union_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : PreOpen (A : Set X)) : PreOpen (A ∪ interior (A : Set X)) := by
  have hOpen : IsOpen (interior (A : Set X)) := isOpen_interior
  simpa using PreOpen.union_open (A := A) (U := interior A) hA hOpen

end Topology

namespace Topology

theorem closure_inter_interior_eq_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (A : Set X) ∩ interior (A : Set X) = interior (A : Set X) := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hxInt
    have hxA : x ∈ (A : Set X) := interior_subset hxInt
    have hxCl : x ∈ closure (A : Set X) := subset_closure hxA
    exact ⟨hxCl, hxInt⟩

end Topology

theorem interior_inter_closure_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A : Set X) ∩ closure (B : Set X) ⊆
      closure (A ∩ B : Set X) := by
  intro x hx
  have hxInt : x ∈ interior (A : Set X) := hx.1
  have hxCl  : x ∈ closure (B : Set X) := hx.2
  -- Use the neighbourhood characterisation of the closure.
  apply (mem_closure_iff).2
  intro V hVopen hxV
  -- The auxiliary open neighbourhood `V ∩ interior A`.
  have hVIntOpen : IsOpen (V ∩ interior (A : Set X)) :=
    hVopen.inter isOpen_interior
  have hxVInt : x ∈ V ∩ interior (A : Set X) := ⟨hxV, hxInt⟩
  -- Since `x ∈ closure B`, this neighbourhood meets `B`.
  have hNonempty : ((V ∩ interior (A : Set X)) ∩ B).Nonempty :=
    (mem_closure_iff).1 hxCl (V ∩ interior A) hVIntOpen hxVInt
  -- Rearrange the intersection to fit the required shape.
  rcases hNonempty with ⟨y, ⟨hyV, hyIntA⟩, hyB⟩
  have hyA : y ∈ (A : Set X) := interior_subset hyIntA
  exact ⟨y, ⟨hyV, ⟨hyA, hyB⟩⟩⟩

namespace Topology

variable {X : Type*} [TopologicalSpace X]

theorem PreOpen.alphaOpen_iff_semiOpen {A : Set X}
    (hPre : PreOpen (A : Set X)) :
    AlphaOpen (A : Set X) ↔ SemiOpen (A : Set X) := by
  constructor
  · intro hAlpha
    exact AlphaOpen.to_SemiOpen hAlpha
  · intro hSemi
    exact AlphaOpen.of_PreOpen_and_SemiOpen hPre hSemi

end Topology

theorem closure_union_subset_union_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∪ B : Set X) ⊆ closure (A : Set X) ∪ closure (B : Set X) := by
  -- The set on the right is closed and contains `A ∪ B`.
  have hClosed : IsClosed (closure (A : Set X) ∪ closure (B : Set X)) :=
    (isClosed_closure : IsClosed (closure (A : Set X))).union
      (isClosed_closure : IsClosed (closure (B : Set X)))
  have hSubset : (A ∪ B : Set X) ⊆ closure A ∪ closure B := by
    intro x hx
    cases hx with
    | inl hxA => exact Or.inl (subset_closure hxA)
    | inr hxB => exact Or.inr (subset_closure hxB)
  -- Apply the minimality of the closure.
  exact closure_minimal hSubset hClosed

theorem Topology.closure_subset_of_subset_SemiOpen {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : (A : Set X) ⊆ B) (hB : Topology.SemiOpen (B : Set X)) :
    closure (A : Set X) ⊆ closure (interior (B : Set X)) := by
  calc
    closure (A : Set X) ⊆ closure (B : Set X) :=
      closure_mono hAB
    _ ⊆ closure (interior (B : Set X)) :=
      Topology.SemiOpen.closure_subset hB

theorem PreOpen_interior_closure_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.PreOpen (interior (closure (interior (closure A)))) := by
  have hOpen : IsOpen (interior (closure (interior (closure A)))) :=
    isOpen_interior
  simpa using (IsOpen.to_PreOpen hOpen)

theorem IsOpen.semiopen_iff_alphaopen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.SemiOpen (A : Set X) ↔ Topology.AlphaOpen (A : Set X) := by
  constructor
  · intro _hSemi
    exact IsOpen.to_AlphaOpen hA
  · intro hAlpha
    exact Topology.AlphaOpen.to_SemiOpen hAlpha



theorem Topology.PreOpen_iff_exists_closed_superset_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    PreOpen (A : Set X) ↔
      ∃ F : Set X, IsClosed F ∧ A ⊆ interior F ∧ F ⊆ closure (A : Set X) := by
  constructor
  · intro hA
    exact
      Topology.PreOpen.exists_closed_superset_subset_closure (A := A) hA
  · rintro ⟨F, hFclosed, hAintF, hFsubset⟩
    unfold Topology.PreOpen
    intro x hxA
    have hxIntF : x ∈ interior F := hAintF hxA
    have hIntSubset : interior F ⊆ interior (closure (A : Set X)) :=
      interior_mono hFsubset
    exact hIntSubset hxIntF

namespace Topology

theorem AlphaOpen.exists_closed_superset_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : AlphaOpen (A : Set X)) :
    ∃ F : Set X, IsClosed F ∧ A ⊆ interior F ∧ F ⊆ closure (interior A) := by
  refine ⟨closure (interior A), isClosed_closure, ?_, subset_rfl⟩
  intro x hxA
  exact hA hxA

end Topology

theorem IsOpen.preopen_iff_semiopen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.PreOpen (A : Set X) ↔ Topology.SemiOpen (A : Set X) := by
  -- Relate both notions to `AlphaOpen`.
  have h₁ := IsOpen.preopen_iff_alphaopen (A := A) hA
  have h₂ := IsOpen.semiopen_iff_alphaopen (A := A) hA
  -- Combine the two equivalences.
  exact h₁.trans h₂.symm

theorem Topology.SemiOpen_iff_pointwise {X : Type*} [TopologicalSpace X] {A : Set X} :
    SemiOpen (A : Set X) ↔
      ∀ x, x ∈ A →
        ∀ V : Set X, IsOpen V → x ∈ V →
          (V ∩ interior (A : Set X)).Nonempty := by
  unfold SemiOpen
  -- First, show that `SemiOpen` implies the pointwise neighbourhood property.
  constructor
  · intro hSemi x hxA V hVopen hxV
    -- From semi-openness we know `x ∈ closure (interior A)`.
    have hxCl : x ∈ closure (interior (A : Set X)) := hSemi hxA
    -- Use the neighbourhood characterisation of the closure.
    have hNonempty : ((V ∩ interior (A : Set X)) : Set X).Nonempty :=
      (mem_closure_iff).1 hxCl V hVopen hxV
    -- Rearrange the intersection to the desired shape.
    simpa [Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using hNonempty
  -- Conversely, assume the pointwise property and prove `SemiOpen`.
  · intro hPointwise x hxA
    -- We show `x ∈ closure (interior A)` using `mem_closure_iff`.
    apply (mem_closure_iff).2
    intro V hVopen hxV
    -- Apply the given pointwise condition to obtain the required intersection.
    have hNonempty : ((V ∩ interior (A : Set X)) : Set X).Nonempty :=
      hPointwise x hxA V hVopen hxV
    simpa [Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using hNonempty



theorem Topology.PreOpen.union_interior_closure_eq {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : Topology.PreOpen (A : Set X)) :
    (A : Set X) ∪ interior (closure (A : Set X)) =
      interior (closure (A : Set X)) := by
  ext x
  constructor
  · intro hx
    cases hx with
    | inl hxA => exact hA hxA
    | inr hxInt => exact hxInt
  · intro hxInt
    exact Or.inr hxInt

namespace Topology

theorem SemiOpen.union_closure_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : SemiOpen (A : Set X)) :
    (A : Set X) ∪ closure (interior (A : Set X)) =
      closure (interior (A : Set X)) := by
  -- `A` is contained in `closure (interior A)` by semi-openness.
  have hSubset : (A : Set X) ⊆ closure (interior (A : Set X)) := hA
  -- Establish the desired set equality.
  ext x
  constructor
  · intro hx
    cases hx with
    | inl hxA   => exact hSubset hxA
    | inr hxClI => exact hxClI
  · intro hxClI
    exact Or.inr hxClI

end Topology



theorem Topology.SemiOpen.closure_diff_interior_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.SemiOpen (A : Set X)) :
    closure (A \ interior (A : Set X)) ⊆ closure (interior (A : Set X)) := by
  -- First, `A \ interior A` is contained in `A`.
  have hSubset : (A \ interior (A : Set X) : Set X) ⊆ A := Set.diff_subset
  -- Hence their closures satisfy the same inclusion.
  have hClSubset : closure (A \ interior (A : Set X)) ⊆ closure (A : Set X) :=
    closure_mono hSubset
  -- From semi-openness, `closure A ⊆ closure (interior A)`.
  have hSemi : closure (A : Set X) ⊆ closure (interior (A : Set X)) :=
    Topology.SemiOpen.closure_subset hA
  -- Combine the two inclusions.
  exact Set.Subset.trans hClSubset hSemi

theorem Topology.AlphaOpen.union_interior_closure_interior_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.AlphaOpen (A : Set X)) :
    (A : Set X) ∪ interior (closure (interior (A : Set X))) =
      interior (closure (interior (A : Set X))) := by
  ext x
  constructor
  · intro hx
    cases hx with
    | inl hxA   => exact hA hxA
    | inr hxInt => exact hxInt
  · intro hxInt
    exact Or.inr hxInt

namespace Topology

variable {X : Type*} [TopologicalSpace X]

/--  
If `A` is semi-open and `B ⊆ A`, then  
`closure B ⊆ closure (interior A)`.  
-/
theorem SemiOpen.closure_subset_of_subset
    {A B : Set X} (hA : SemiOpen (A : Set X)) (hBA : (B : Set X) ⊆ A) :
    closure (B : Set X) ⊆ closure (interior (A : Set X)) := by
  intro x hxClB
  -- First, upgrade the subset relation using semi-openness of `A`.
  have hBsubset : (B : Set X) ⊆ closure (interior (A : Set X)) := by
    intro y hyB
    exact hA (hBA hyB)
  -- Apply monotonicity of `closure`.
  have hx' : x ∈ closure (closure (interior (A : Set X))) :=
    closure_mono hBsubset hxClB
  -- Simplify the double closure.
  simpa [closure_closure] using hx'

end Topology



namespace Topology

variable {X : Type*} [TopologicalSpace X]

/--  
If every set in a family is preopen, then the closure of their union is semi-open.  
-/
theorem PreOpen.iUnion_closure_SemiOpen {ι : Sort*} {A : ι → Set X}
    (hA : ∀ i, PreOpen (A i)) :
    SemiOpen (closure (⋃ i, A i)) := by
  -- First, the union itself is preopen.
  have hPre : PreOpen (⋃ i, A i) := PreOpen.iUnion hA
  -- The closure of a preopen set is semi-open.
  exact PreOpen.closure_SemiOpen hPre

end Topology

theorem Topology.interior_union_closure_compl_univ
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A : Set X) ∪ closure ((A : Set X)ᶜ) = (Set.univ : Set X) := by
  classical
  ext x
  constructor
  · intro _hx
    exact Set.mem_univ x
  · intro _hx
    by_cases hxInt : x ∈ interior (A : Set X)
    · exact Or.inl hxInt
    · -- Otherwise, we show `x ∈ closure (Aᶜ)`.
      have hxCl : x ∈ closure ((A : Set X)ᶜ) := by
        -- Neighbourhood characterisation of the closure.
        apply (mem_closure_iff).2
        intro V hVopen hxV
        -- We prove that `V ∩ Aᶜ` is nonempty.
        by_contra hEmpty
        -- If the intersection is empty, then `V ⊆ A`.
        have hVsubsetA : (V : Set X) ⊆ A := by
          intro y hyV
          by_contra hyNotA
          have : y ∈ (V ∩ ((A : Set X)ᶜ)) := ⟨hyV, hyNotA⟩
          have : ((V ∩ ((A : Set X)ᶜ)) : Set X).Nonempty := ⟨y, this⟩
          exact hEmpty this
        -- Hence `x` belongs to an open neighbourhood contained in `A`,
        -- contradicting `x ∉ interior A`.
        have hxInt' : x ∈ interior (A : Set X) := by
          have hVnhds : (V : Set X) ∈ 𝓝 x := hVopen.mem_nhds hxV
          have hAnhds : (A : Set X) ∈ 𝓝 x :=
            Filter.mem_of_superset hVnhds hVsubsetA
          exact (mem_interior_iff_mem_nhds).2 hAnhds
        exact (hxInt hxInt').elim
      exact Or.inr hxCl

theorem Topology.SemiOpen.interior_closure_subset {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : Topology.SemiOpen (A : Set X)) :
    interior (closure (A : Set X)) ⊆ closure (interior (A : Set X)) := by
  intro x hx
  -- From `hx` we know `x` lies in `closure A`.
  have hxCl : x ∈ closure (A : Set X) := interior_subset hx
  -- Semi-openness gives the inclusion of closures.
  have hIncl : closure (A : Set X) ⊆ closure (interior (A : Set X)) :=
    Topology.SemiOpen.closure_subset hA
  -- Combine the two facts.
  exact hIncl hxCl

namespace Topology

variable {X : Type*} [TopologicalSpace X]

theorem AlphaOpen.of_PreOpen_and_closure_eq
    {A : Set X} (hPre : PreOpen (A : Set X))
    (hEq : closure (A : Set X) = closure (interior (A : Set X))) :
    AlphaOpen (A : Set X) := by
  -- Turn the closure equality into `SemiOpen A`.
  have hSemi : SemiOpen (A : Set X) :=
    (SemiOpen_iff_closure_eq_closure_interior (A := A)).2 hEq
  -- Combine `PreOpen` and `SemiOpen` to obtain `AlphaOpen`.
  exact AlphaOpen.of_PreOpen_and_SemiOpen hPre hSemi

end Topology

theorem Topology.SemiOpen.inter_closure_interior_eq_self
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.SemiOpen (A : Set X)) :
    (A : Set X) ∩ closure (interior (A : Set X)) = (A : Set X) := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hxA
    have hxCl : x ∈ closure (interior (A : Set X)) := hA hxA
    exact ⟨hxA, hxCl⟩

theorem closure_union_eq_union_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∪ B : Set X) = closure (A : Set X) ∪ closure (B : Set X) := by
  apply Set.Subset.antisymm
  · exact closure_union_subset_union_closure
  · exact closure_union_subset

namespace Topology

theorem interior_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) ⊆ closure (A : Set X) := by
  intro x hxInt
  -- From `hxInt` we know `x ∈ A`.
  have hxA : x ∈ (A : Set X) := interior_subset hxInt
  -- Every point of a set lies in the closure of that set.
  exact subset_closure hxA

end Topology

theorem Topology.SemiOpen.boundary_eq_closureInterior_diff_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.SemiOpen (A : Set X)) :
    closure (A : Set X) \ interior (A : Set X) =
      closure (interior (A : Set X)) \ interior (A : Set X) := by
  -- For a semi-open set, the two closures coincide.
  have hCl :
      closure (A : Set X) = closure (interior (A : Set X)) :=
    Topology.SemiOpen.closure_eq_closure_interior (A := A) hA
  -- Rewrite the difference using this equality.
  simpa [Set.diff_eq, hCl]

namespace Topology

variable {X : Type*} [TopologicalSpace X]

theorem PreOpen.closure_subset_of_subset {A B : Set X}
    (hB : PreOpen (B : Set X)) (hAB : (A : Set X) ⊆ B) :
    closure (A : Set X) ⊆ closure (interior (closure (B : Set X))) := by
  -- From `hAB` and the fact that `B` is preopen we get  
  -- `A ⊆ interior (closure B)`.
  have hSubset : (A : Set X) ⊆ interior (closure (B : Set X)) := by
    intro x hxA
    exact hB (hAB hxA)
  -- Taking closures preserves inclusions.
  exact closure_mono hSubset

end Topology



theorem Topology.PreOpen.nonempty_iff_interior_closure_nonempty
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.PreOpen (A : Set X)) :
    (A : Set X).Nonempty ↔ (interior (closure (A : Set X))).Nonempty := by
  classical
  constructor
  · intro hANonempty
    exact Topology.PreOpen.interior_closure_nonempty_of_nonempty hA hANonempty
  · intro hIntNonempty
    by_cases hANonempty : (A : Set X).Nonempty
    · exact hANonempty
    · -- Assuming `A` is empty contradicts `hIntNonempty`.
      have hAempty : (A : Set X) = ∅ := by
        ext y
        constructor
        · intro hy
          have : (A : Set X).Nonempty := ⟨y, hy⟩
          exact (hANonempty this).elim
        · intro hy
          cases hy
      -- Under `A = ∅`, the interior of its closure is empty.
      have hIntEq : interior (closure (A : Set X)) = (∅ : Set X) := by
        simpa [hAempty, closure_empty, interior_empty]
      rcases hIntNonempty with ⟨x, hxInt⟩
      have : x ∈ (∅ : Set X) := by
        simpa [hIntEq] using hxInt
      cases this

namespace Topology

theorem SemiOpen.frontier_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : SemiOpen (A : Set X)) :
    frontier (A : Set X) ⊆ closure (interior (A : Set X)) := by
  intro x hx
  rcases hx with ⟨hxClA, _hxNotIntA⟩
  exact (SemiOpen.closure_subset hA) hxClA

end Topology

namespace Topology

theorem AlphaOpen.frontier_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : AlphaOpen (A : Set X)) :
    frontier (A : Set X) ⊆ closure (interior (A : Set X)) := by
  intro x hx
  -- `x` lies in the frontier, hence in the closure of `A`.
  have hxCl : x ∈ closure (A : Set X) := hx.1
  -- For an α-open set we have `closure A ⊆ closure (interior A)`.
  have hIncl : closure (A : Set X) ⊆ closure (interior (A : Set X)) :=
    AlphaOpen.closure_subset hA
  exact hIncl hxCl

end Topology

namespace Topology

theorem PreOpen.frontier_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : PreOpen (A : Set X)) :
    frontier (A : Set X) ⊆ closure (interior (closure (A : Set X))) := by
  intro x hx
  -- From `hx`, the point `x` lies in `closure A`.
  have hxCl : x ∈ closure (A : Set X) := hx.1
  -- Because `A` is preopen, we have `A ⊆ interior (closure A)`.
  have hSubset : (A : Set X) ⊆ interior (closure (A : Set X)) := hA
  -- Taking closures preserves inclusions.
  have hClosure :
      closure (A : Set X) ⊆ closure (interior (closure (A : Set X))) :=
    closure_mono hSubset
  -- Conclude the desired membership.
  exact hClosure hxCl

end Topology

namespace Topology

theorem SemiOpen.frontier_eq_closureInterior_diff_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : SemiOpen (A : Set X)) :
    frontier (A : Set X) =
      closure (interior (A : Set X)) \ interior (A : Set X) := by
  -- For any set, `frontier A = closure A \ interior A`.
  -- For a semi-open set, the two closures coincide.
  have hCl :
      closure (A : Set X) = closure (interior (A : Set X)) :=
    SemiOpen.closure_eq_closure_interior (A := A) hA
  simpa [frontier, hCl]

end Topology

theorem Topology.SemiOpen.closure_interior_closure_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.SemiOpen (A : Set X)) :
    closure (interior (closure (A : Set X))) =
      closure (interior (A : Set X)) := by
  -- From semi-openness we have equality of the two closures.
  have hCl :
      closure (A : Set X) = closure (interior (A : Set X)) :=
    Topology.SemiOpen.closure_eq_closure_interior (A := A) hA
  -- Taking interiors of equal sets yields equal interiors.
  have hInt :
      interior (closure (A : Set X)) =
        interior (closure (interior (A : Set X))) := by
    simpa using congrArg (fun S : Set X => interior S) hCl
  -- Taking closures once more preserves the equality.
  have hIntCl :
      closure (interior (closure (A : Set X))) =
        closure (interior (closure (interior (A : Set X)))) := by
    simpa using congrArg (fun S : Set X => closure S) hInt
  -- A general lemma simplifies the right‐hand side.
  have hSimpl :
      closure (interior (closure (interior (A : Set X)))) =
        closure (interior (A : Set X)) :=
    Topology.closure_interior_closure_interior_eq_closure_interior (A := A)
  -- Combine the equalities.
  simpa [hIntCl] using hSimpl

theorem Set.compl_compl {α : Type*} (s : Set α) : sᶜᶜ = (s : Set α) := by
  ext x
  simp

theorem Topology.AlphaOpen.interior_closure_subset {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : Topology.AlphaOpen (A : Set X)) :
    interior (closure (A : Set X)) ⊆ closure (interior (A : Set X)) := by
  have hSemi : Topology.SemiOpen (A : Set X) :=
    Topology.AlphaOpen.to_SemiOpen hA
  exact Topology.SemiOpen.interior_closure_subset (A := A) hSemi

namespace Topology

variable {X : Type*} [TopologicalSpace X]

theorem AlphaOpen.frontier_eq_closureInterior_diff_interior
    {A : Set X} (hA : AlphaOpen (A : Set X)) :
    frontier (A : Set X) =
      closure (interior (A : Set X)) \ interior (A : Set X) := by
  -- For an α-open set, the two closures coincide.
  have hCl :
      closure (A : Set X) = closure (interior (A : Set X)) :=
    AlphaOpen.closure_eq_closure_interior (A := A) hA
  -- Rewrite the definition of `frontier` using this equality.
  simpa [frontier, hCl]

end Topology



theorem Topology.AlphaOpen.iUnion_closure_SemiOpen
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X}
    (hA : ∀ i, Topology.AlphaOpen (A i)) :
    Topology.SemiOpen (closure (⋃ i, A i)) := by
  -- Each α-open set is preopen.
  have hPre : ∀ i, Topology.PreOpen (A i) := fun i =>
    Topology.AlphaOpen.to_PreOpen (hA i)
  -- Apply the corresponding lemma for preopen sets.
  exact Topology.PreOpen.iUnion_closure_SemiOpen hPre

namespace Topology

theorem interior_closure_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (A : Set X)))) =
      interior (closure (A : Set X)) := by
  -- Introduce an auxiliary notation for `closure A`.
  set C : Set X := closure (A : Set X) with hC
  -- We prove the statement with `C` instead of `closure A`.
  have h : interior (closure (interior C)) = interior C := by
    -- Establish the two inclusions separately.
    apply Set.Subset.antisymm
    · -- `⊆` direction.
      intro x hx
      -- Because `closure (interior C) ⊆ C`, monotonicity of `interior` gives the claim.
      have hsubset : closure (interior C) ⊆ C := by
        -- First, `interior C ⊆ C`.
        have : (interior C : Set X) ⊆ C := interior_subset
        -- Taking closures preserves inclusions.
        have : closure (interior C) ⊆ closure C := closure_mono this
        -- But `closure C = C` since `C` is already closed.
        simpa [closure_closure, hC] using this
      exact (interior_mono hsubset) hx
    · -- `⊇` direction.
      intro x hxC
      -- `interior C` is an open neighbourhood of `x`.
      have hOpen : IsOpen (interior C) := isOpen_interior
      have hNhds : interior C ∈ 𝓝 x := hOpen.mem_nhds hxC
      -- Since `interior C ⊆ closure (interior C)`, the latter is also a neighbourhood of `x`.
      have hSubset : (interior C : Set X) ⊆ closure (interior C) := subset_closure
      have hNhds' : closure (interior C) ∈ 𝓝 x :=
        Filter.mem_of_superset hNhds hSubset
      -- Hence `x` lies in the interior of `closure (interior C)`.
      exact (mem_interior_iff_mem_nhds).2 hNhds'
  -- Re‐express the result in terms of the original set `A`.
  simpa [hC] using h

end Topology

namespace Topology

theorem isClosed_closure_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsClosed (closure (interior (closure (A : Set X)))) := by
  simpa using
    (isClosed_closure :
      IsClosed (closure (interior (closure (A : Set X)))))

end Topology

theorem Topology.SemiOpen.of_frontier_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : frontier (A : Set X) ⊆ closure (interior (A : Set X))) :
    Topology.SemiOpen (A : Set X) := by
  unfold Topology.SemiOpen at *
  intro x hxA
  by_cases hxInt : x ∈ interior (A : Set X)
  · -- Case 1: `x` lies in `interior A`, hence in `closure (interior A)`.
    exact subset_closure hxInt
  · -- Case 2: `x` does **not** lie in `interior A`.
    -- Then `x` lies in `frontier A` because it is in `A ⊆ closure A`
    -- and not in `interior A`.
    have hxFrontier : x ∈ frontier (A : Set X) := by
      have hxCl : x ∈ closure (A : Set X) := subset_closure hxA
      exact ⟨hxCl, hxInt⟩
    -- Apply the hypothesis controlling the frontier.
    exact h hxFrontier

theorem Topology.PreOpen.inter_interior_closure_eq_self
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.PreOpen (A : Set X)) :
    (A : Set X) ∩ interior (closure (A : Set X)) = A := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hxA
    exact ⟨hxA, hA hxA⟩

theorem SemiOpen_closureInterior_union_interiorClosure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.SemiOpen (closure (interior A) ∪ interior (closure A)) := by
  -- `closure (interior A)` is semi-open.
  have hClInt : Topology.SemiOpen (closure (interior A)) := by
    simpa using (SemiOpen_closure_interior (A := A))
  -- `interior (closure A)` is an open set, hence semi-open.
  have hIntCl : Topology.SemiOpen (interior (closure A)) := by
    have hOpen : IsOpen (interior (closure A)) := isOpen_interior
    simpa using (IsOpen.to_SemiOpen hOpen)
  -- The union of two semi-open sets is semi-open.
  simpa using
    (SemiOpen.union (A := closure (interior A))
      (B := interior (closure A)) hClInt hIntCl)

theorem Topology.AlphaOpen.inter_closure_interior_eq_self
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.AlphaOpen (A : Set X)) :
    (A : Set X) ∩ closure (interior (A : Set X)) = A := by
  -- An α-open set is semi-open, so we can reuse the corresponding lemma.
  have hSemi : Topology.SemiOpen (A : Set X) :=
    Topology.AlphaOpen.to_SemiOpen hA
  simpa using
    Topology.SemiOpen.inter_closure_interior_eq_self (A := A) hSemi

theorem Topology.SemiOpen.iUnion_closure_SemiOpen {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {A : ι → Set X} (hA : ∀ i, Topology.SemiOpen (A i)) :
    Topology.SemiOpen (closure (⋃ i, A i)) := by
  -- First, the union itself is semi-open.
  have hUnion : Topology.SemiOpen (⋃ i, A i) := SemiOpen.iUnion hA
  -- The closure of a semi-open set is semi-open.
  simpa using
    (Topology.SemiOpen.closure_SemiOpen (A := ⋃ i, A i) hUnion)

namespace Topology

theorem SemiOpen_iff_frontier_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    SemiOpen (A : Set X) ↔
      frontier (A : Set X) ⊆ closure (interior (A : Set X)) := by
  constructor
  · intro hSemi
    exact SemiOpen.frontier_subset_closure_interior (A := A) hSemi
  · intro hSubset
    exact SemiOpen.of_frontier_subset_closure_interior (A := A) hSubset

end Topology



namespace Topology

theorem PreOpen.sUnion_closure_SemiOpen {X : Type*} [TopologicalSpace X]
    {𝒜 : Set (Set X)} (h𝒜 : ∀ S, S ∈ 𝒜 → PreOpen S) :
    SemiOpen (closure (⋃₀ 𝒜)) := by
  -- First, the sUnion itself is preopen.
  have hPre : PreOpen (⋃₀ 𝒜) := PreOpen.sUnion (𝒜 := 𝒜) h𝒜
  -- The closure of a preopen set is semi-open.
  exact PreOpen.closure_SemiOpen hPre

end Topology

namespace Topology

variable {X : Type*} [TopologicalSpace X]

theorem PreOpen.union_closure_SemiOpen {A B : Set X}
    (hA : PreOpen (A : Set X)) (hB : PreOpen (B : Set X)) :
    SemiOpen (closure (A ∪ B : Set X)) := by
  -- The union of two preopen sets is preopen.
  have hUnion : PreOpen (A ∪ B : Set X) := PreOpen.union (A := A) (B := B) hA hB
  -- The closure of a preopen set is semi-open.
  exact PreOpen.closure_SemiOpen (A := A ∪ B) hUnion

end Topology

theorem IsOpen.closure_eq_closure_interior' {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen (A : Set X)) :
    closure (interior (A : Set X)) = closure (A : Set X) := by
  -- First inclusion: `closure (interior A) ⊆ closure A`
  have h₁ :
      closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
    closure_mono (interior_subset : interior (A : Set X) ⊆ A)
  -- Second inclusion: `closure A ⊆ closure (interior A)`
  have h₂ :
      closure (A : Set X) ⊆ closure (interior (A : Set X)) := by
    -- Since `A` is open, every point of `A` actually lies in `interior A`.
    have hSub : (A : Set X) ⊆ interior (A : Set X) := by
      intro x hxA
      have hNhds : (A : Set X) ∈ 𝓝 x := hA.mem_nhds hxA
      exact (mem_interior_iff_mem_nhds).2 hNhds
    exact closure_mono hSub
  exact Set.Subset.antisymm h₁ h₂

theorem closure_eq_self_union_frontier
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (A : Set X) = A ∪ frontier (A : Set X) := by
  ext x
  constructor
  · intro hxCl
    by_cases hxInt : x ∈ interior (A : Set X)
    · -- If `x ∈ interior A`, then `x ∈ A`.
      exact .inl (interior_subset hxInt)
    · -- Otherwise `x` belongs to the frontier.
      have : x ∈ frontier (A : Set X) := by
        exact ⟨hxCl, hxInt⟩
      exact .inr this
  · intro hx
    cases hx with
    | inl hxA =>
        -- Points of `A` certainly lie in its closure.
        exact subset_closure hxA
    | inr hxFrontier =>
        -- By definition, points of the frontier lie in the closure.
        exact hxFrontier.1

namespace Topology

theorem AlphaOpen.closure_diff_interior_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : AlphaOpen (A : Set X)) :
    closure (A \ interior (A : Set X)) ⊆ closure (interior (A : Set X)) := by
  -- An α-open set is semi-open.
  have hSemi : SemiOpen (A : Set X) := AlphaOpen.to_SemiOpen hA
  -- Apply the corresponding lemma for semi-open sets.
  exact
    SemiOpen.closure_diff_interior_subset_closure_interior (A := A) hSemi

end Topology

namespace Topology

theorem SemiOpen.frontier_eq_frontier_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : SemiOpen (A : Set X)) :
    frontier (A : Set X) = frontier (interior (A : Set X)) := by
  -- Express the frontier of `A` via `closure (interior A)` and `interior A`.
  have h₁ :
      frontier (A : Set X) =
        closure (interior (A : Set X)) \ interior (A : Set X) :=
    SemiOpen.frontier_eq_closureInterior_diff_interior (A := A) hA
  -- Do the same for the frontier of `interior A`.
  have h₂ :
      frontier (interior (A : Set X)) =
        closure (interior (A : Set X)) \ interior (A : Set X) := by
    -- Since `frontier S = closure S \ interior S` and
    -- `interior (interior A) = interior A`, this is immediate.
    simpa [frontier, interior_interior]
  -- Combine the two characterisations.
  calc
    frontier (A : Set X)
        = closure (interior (A : Set X)) \ interior (A : Set X) := h₁
    _ = frontier (interior (A : Set X)) := by
      simpa [h₂.symm]

end Topology

theorem frontier_union_subset_union_frontier
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier (A ∪ B : Set X) ⊆
      frontier (A : Set X) ∪ frontier (B : Set X) := by
  intro x hx
  -- Decompose the membership in the frontier of `A ∪ B`.
  have hxCl : x ∈ closure (A ∪ B : Set X) := hx.1
  have hxNotInt : x ∉ interior (A ∪ B : Set X) := hx.2
  -- `interior A` and `interior B` are contained in `interior (A ∪ B)`.
  have hIntA_subset :
      interior (A : Set X) ⊆ interior (A ∪ B : Set X) :=
    interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
  have hIntB_subset :
      interior (B : Set X) ⊆ interior (A ∪ B : Set X) :=
    interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
  -- Hence `x` is not in `interior A` nor in `interior B`.
  have hxNotIntA : x ∉ interior (A : Set X) := by
    intro hxIntA
    exact hxNotInt (hIntA_subset hxIntA)
  have hxNotIntB : x ∉ interior (B : Set X) := by
    intro hxIntB
    exact hxNotInt (hIntB_subset hxIntB)
  -- A point in `closure (A ∪ B)` lies in the closure of one of the two sets.
  have hCl_subset :
      closure (A ∪ B : Set X) ⊆ closure (A : Set X) ∪ closure (B : Set X) :=
    closure_union_subset_union_closure
  have hxClUnion : x ∈ closure (A : Set X) ∪ closure (B : Set X) :=
    hCl_subset hxCl
  -- Conclude that `x` lies in one of the two frontiers.
  cases hxClUnion with
  | inl hxClA =>
      exact Or.inl ⟨hxClA, hxNotIntA⟩
  | inr hxClB =>
      exact Or.inr ⟨hxClB, hxNotIntB⟩

set_option maxRecDepth 10000

theorem frontier_interior_subset_frontier {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    frontier (interior (A : Set X)) ⊆ frontier (A : Set X) := by
  intro x hx
  -- `hx` gives that `x` lies in the closure of `interior A`
  -- and not in the interior of `interior A`.
  have hx_cl_int : x ∈ closure (interior (A : Set X)) := hx.1
  have hx_not_int_int : x ∉ interior (interior (A : Set X)) := hx.2
  -- Monotonicity of `closure` yields
  -- `closure (interior A) ⊆ closure A`.
  have h_cl_subset : closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
    closure_mono (interior_subset : interior (A : Set X) ⊆ A)
  have hx_clA : x ∈ closure (A : Set X) := h_cl_subset hx_cl_int
  -- Since `interior (interior A) = interior A`,
  -- we translate the non-membership information.
  have hx_not_intA : x ∉ interior (A : Set X) := by
    simpa [interior_interior] using hx_not_int_int
  -- Combine the two facts to obtain membership in the desired frontier.
  exact ⟨hx_clA, hx_not_intA⟩

namespace Topology

variable {X : Type*} [TopologicalSpace X]

theorem AlphaOpen.frontier_eq_frontier_interior
    {A : Set X} (hA : AlphaOpen (A : Set X)) :
    frontier (A : Set X) = frontier (interior (A : Set X)) := by
  -- An α-open set is semi-open, so we can reuse the corresponding lemma.
  have hSemi : SemiOpen (A : Set X) := AlphaOpen.to_SemiOpen hA
  simpa using
    SemiOpen.frontier_eq_frontier_interior (A := A) hSemi

end Topology

theorem interior_subset_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) ⊆
      interior (closure (interior (A : Set X))) := by
  intro x hx
  -- Reinterpret `hx` as membership in `interior (interior A)`.
  have hx' : x ∈ interior (interior (A : Set X)) := by
    simpa [interior_interior] using hx
  -- Monotonicity of `interior` applied to
  -- `interior A ⊆ closure (interior A)`.
  have hSubset :
      interior (interior (A : Set X)) ⊆
        interior (closure (interior (A : Set X))) := by
    apply interior_mono
    exact (subset_closure :
      interior (A : Set X) ⊆ closure (interior (A : Set X)))
  exact hSubset hx'



theorem IsClosed.closure_interior_eq_of_AlphaOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X))
    (hA_alpha : Topology.AlphaOpen (A : Set X)) :
    closure (interior (A : Set X)) = A := by
  -- An α-open set is semi-open.
  have hA_semi : Topology.SemiOpen (A : Set X) :=
    Topology.AlphaOpen.to_SemiOpen hA_alpha
  -- Apply the closed + semi-open result.
  simpa using
    IsClosed.closure_interior_eq_of_SemiOpen (A := A) hA_closed hA_semi

theorem frontier_inter_subset_frontier {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    frontier (A ∩ B : Set X) ⊆
      frontier (A : Set X) ∪ frontier (B : Set X) := by
  intro x hx
  -- Decompose the hypothesis `hx`.
  have hxCl  : x ∈ closure (A ∩ B : Set X) := hx.1
  have hxNot : x ∉ interior (A ∩ B : Set X) := hx.2
  -- `x` lies in the closure of each factor.
  have hxClA : x ∈ closure (A : Set X) :=
    (closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)) hxCl
  have hxClB : x ∈ closure (B : Set X) :=
    (closure_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)) hxCl
  -- We analyse the interior membership.
  by_cases hIntA : x ∈ interior (A : Set X)
  · by_cases hIntB : x ∈ interior (B : Set X)
    · -- If `x` is in both interiors, it lies in `interior (A ∩ B)`, contradiction.
      have hOpen : IsOpen (interior (A : Set X) ∩ interior (B : Set X)) :=
        isOpen_interior.inter isOpen_interior
      have hxMem : x ∈ interior (A : Set X) ∩ interior (B : Set X) :=
        ⟨hIntA, hIntB⟩
      have hSubset :
          (interior (A : Set X) ∩ interior (B : Set X) : Set X) ⊆
            A ∩ B := by
        intro y hy; exact ⟨interior_subset hy.1, interior_subset hy.2⟩
      have hxIntAB : x ∈ interior (A ∩ B : Set X) :=
        (mem_interior_iff_mem_nhds).2
          (Filter.mem_of_superset (hOpen.mem_nhds hxMem) hSubset)
      exact (hxNot hxIntAB).elim
    · -- Not in `interior B` ⇒ `x ∈ frontier B`.
      exact Or.inr ⟨hxClB, hIntB⟩
  · -- Not in `interior A` ⇒ `x ∈ frontier A`.
    exact Or.inl ⟨hxClA, hIntA⟩

theorem closure_eq_interior_union_frontier {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (A : Set X) = interior (A : Set X) ∪ frontier (A : Set X) := by
  ext x
  constructor
  · intro hxCl
    by_cases hxInt : x ∈ interior (A : Set X)
    · exact Or.inl hxInt
    · have hxFront : x ∈ frontier (A : Set X) := by
        exact ⟨hxCl, hxInt⟩
      exact Or.inr hxFront
  · intro h
    cases h with
    | inl hxInt =>
        -- `interior A ⊆ A` and `A ⊆ closure A`
        have hxA : x ∈ (A : Set X) := interior_subset hxInt
        exact subset_closure hxA
    | inr hxFront =>
        exact hxFront.1

theorem IsOpen.frontier_eq_closure_diff {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    frontier (A : Set X) = closure (A : Set X) \ A := by
  simp [frontier, hA.interior_eq]

theorem IsOpen.inter_PreOpen {X : Type*} [TopologicalSpace X] {A U : Set X}
    (hU : IsOpen (U : Set X)) (hA : Topology.PreOpen (A : Set X)) :
    Topology.PreOpen (U ∩ A : Set X) := by
  simpa [Set.inter_comm] using
    (Topology.PreOpen.inter_open (A := A) (U := U) hA hU)

namespace Topology

/--
If `A` is α-open and `B ⊆ A`, then  
`closure B ⊆ closure (interior A)`.
-/
theorem AlphaOpen.closure_subset_of_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : AlphaOpen (A : Set X)) (hBA : (B : Set X) ⊆ A) :
    closure (B : Set X) ⊆ closure (interior (A : Set X)) := by
  -- An α-open set is semi-open.
  have hSemi : SemiOpen (A : Set X) := AlphaOpen.to_SemiOpen hA
  -- Apply the corresponding lemma for semi-open sets.
  exact
    SemiOpen.closure_subset_of_subset (A := A) (B := B) hSemi hBA

end Topology

theorem Topology.frontier_subset_closure_compl
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (A : Set X) ⊆ closure (Aᶜ : Set X) := by
  intro x hx
  -- `hx` gives both `x ∈ closure A` and `x ∉ interior A`.
  have hx_not_int : x ∉ interior (A : Set X) := hx.2
  -- To show `x ∈ closure (Aᶜ)`, use the neighbourhood criterion.
  apply (mem_closure_iff).2
  intro V hVopen hxV
  -- Assume, for contradiction, that `V ∩ Aᶜ` is empty.
  by_contra hEmpty
  -- Then `V ⊆ A`.
  have hSubset : (V : Set X) ⊆ A := by
    intro y hy
    by_contra hyNotA
    have : ((V ∩ Aᶜ : Set X)).Nonempty := ⟨y, ⟨hy, hyNotA⟩⟩
    exact hEmpty this
  -- Hence `x` lies in `interior A`, contradicting `hx_not_int`.
  have hx_int : x ∈ interior (A : Set X) := by
    have hVnhds : (V : Set X) ∈ 𝓝 x := hVopen.mem_nhds hxV
    have hAnhds : (A : Set X) ∈ 𝓝 x :=
      Filter.mem_of_superset hVnhds hSubset
    exact (mem_interior_iff_mem_nhds).2 hAnhds
  exact hx_not_int hx_int

namespace Topology

variable {X : Type*} [TopologicalSpace X]

/--
The frontier of a set is the intersection of the closures of the set and its
complement.
-/
theorem frontier_eq_closure_inter_closure_compl (A : Set X) :
    frontier (A : Set X) = closure (A : Set X) ∩ closure (Aᶜ : Set X) := by
  -- Unfold the definition of `frontier`.
  -- `frontier A = closure A \ interior A`.
  ext x
  constructor
  · intro hx
    -- `x` lies in the closure of `A`.
    have hx_clA : x ∈ closure (A : Set X) := hx.1
    -- `x` is not in the interior of `A`.
    have hx_not_intA : x ∉ interior (A : Set X) := hx.2
    -- We show that `x` also lies in the closure of `Aᶜ`.
    have hx_clAc : x ∈ closure (Aᶜ : Set X) := by
      -- Use the neighbourhood characterisation of the closure.
      apply (mem_closure_iff).2
      intro V hVopen hxV
      -- If `V` were contained in `A`, then `x` would lie in `interior A`,
      -- contradicting `hx_not_intA`.
      have : (V : Set X) ⊆ A → False := by
        intro hVsubset
        have hx_intA : x ∈ interior (A : Set X) := by
          have hV_nhds : (V : Set X) ∈ 𝓝 x := hVopen.mem_nhds hxV
          have hA_nhds : (A : Set X) ∈ 𝓝 x :=
            Filter.mem_of_superset hV_nhds hVsubset
          exact (mem_interior_iff_mem_nhds).2 hA_nhds
        exact hx_not_intA hx_intA
      -- Hence `V` is *not* contained in `A`, so it meets `Aᶜ`.
      have hNonempty : ((V ∩ (Aᶜ : Set X)) : Set X).Nonempty := by
        by_contra hEmpty
        have hVsubset : (V : Set X) ⊆ A := by
          intro y hyV
          by_contra hy_notA
          have : y ∈ (V ∩ (Aᶜ : Set X)) := ⟨hyV, hy_notA⟩
          exact hEmpty ⟨y, this⟩
        exact this hVsubset
      -- Provide the required witness.
      simpa [Set.nonempty_def] using hNonempty
    exact ⟨hx_clA, hx_clAc⟩
  · intro hx
    -- `x` lies in the closures of both `A` and `Aᶜ`.
    have hx_clA  : x ∈ closure (A : Set X) := hx.1
    have hx_clAc : x ∈ closure (Aᶜ : Set X) := hx.2
    -- We show `x ∉ interior A`; otherwise we contradict `hx_clAc`.
    have hx_not_intA : x ∉ interior (A : Set X) := by
      intro hx_intA
      -- Use the neighbourhood `interior A` of `x`.
      have hNonempty :
          ((interior (A : Set X)) ∩ (Aᶜ : Set X)).Nonempty :=
        (mem_closure_iff).1 hx_clAc (interior (A : Set X))
          isOpen_interior hx_intA
      rcases hNonempty with ⟨y, hy_int, hy_notA⟩
      exact hy_notA (interior_subset hy_int)
    -- Combine the facts to place `x` in the frontier.
    exact ⟨hx_clA, hx_not_intA⟩

end Topology

theorem frontier_closure_subset_frontier {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    frontier (closure (A : Set X)) ⊆ frontier (A : Set X) := by
  intro x hx
  -- Decompose the membership in the frontier of `closure A`.
  rcases hx with ⟨hxClClA, hxNotIntClA⟩
  -- `closure (closure A)` simplifies to `closure A`.
  have hxClA : x ∈ closure (A : Set X) := by
    simpa [closure_closure] using hxClClA
  -- Likewise for the interior.
  have hxNotIntClA : x ∉ interior (closure (A : Set X)) := by
    simpa [closure_closure] using hxNotIntClA
  -- Since `interior A ⊆ interior (closure A)`, the negation transfers.
  have hxNotIntA : x ∉ interior (A : Set X) := by
    intro hxIntA
    exact hxNotIntClA
      ((interior_mono (subset_closure : (A : Set X) ⊆ closure A)) hxIntA)
  -- Assemble the desired membership.
  exact ⟨hxClA, hxNotIntA⟩

theorem frontier_interior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (interior (A : Set X)) ⊆ closure (A : Set X) := by
  intro x hx
  -- From `hx` we obtain `x ∈ closure (interior A)`.
  have hxCl : x ∈ closure (interior (A : Set X)) := hx.1
  -- Monotonicity of `closure` for the inclusion `interior A ⊆ A`.
  have hIncl :
      closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
    closure_mono (interior_subset : interior (A : Set X) ⊆ A)
  exact hIncl hxCl

namespace Topology

theorem AlphaOpen.iUnion_PreOpen {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {A : ι → Set X} (hA : ∀ i, AlphaOpen (A i)) :
    PreOpen (⋃ i, A i) := by
  -- Every α-open set is preopen.
  have hPre : ∀ i, PreOpen (A i) := fun i => AlphaOpen.to_PreOpen (hA i)
  -- Use the existing `iUnion` lemma for preopen sets.
  exact PreOpen.iUnion hPre

end Topology

theorem closure_frontier_eq {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (frontier (A : Set X)) = frontier (A : Set X) := by
  have hClosed : IsClosed (frontier (A : Set X)) := isClosed_frontier
  simpa using hClosed.closure_eq

theorem interior_subset_interior_union_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (B : Set X) ⊆ interior (A ∪ B : Set X) := by
  exact interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)

theorem Topology.interior_closure_subset_of_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : (B : Set X) ⊆ interior (closure (A : Set X))) :
    interior (closure (B : Set X)) ⊆ interior (closure (A : Set X)) := by
  -- First, upgrade the assumption to an inclusion of closures.
  have hCl : closure (B : Set X) ⊆ closure (A : Set X) :=
    Topology.closure_subset_of_subset_interior_closure (A := A) (B := B) h
  -- Monotonicity of `interior` yields the desired inclusion.
  exact interior_mono hCl

theorem frontier_compl {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (Aᶜ : Set X) = frontier (A : Set X) := by
  -- Express both frontiers via closures of the set and its complement.
  have h₁ :
      frontier (Aᶜ : Set X) =
        closure (Aᶜ : Set X) ∩ closure (A : Set X) := by
    simpa [Set.compl_compl] using
      Topology.frontier_eq_closure_inter_closure_compl
        (A := (Aᶜ : Set X))
  have h₂ :
      frontier (A : Set X) =
        closure (A : Set X) ∩ closure (Aᶜ : Set X) := by
    simpa using
      Topology.frontier_eq_closure_inter_closure_compl (A := (A : Set X))
  -- Combine the two characterisations, using commutativity of `∩`.
  calc
    frontier (Aᶜ : Set X)
        = closure (Aᶜ : Set X) ∩ closure (A : Set X) := h₁
    _ = closure (A : Set X) ∩ closure (Aᶜ : Set X) := by
      simp [Set.inter_comm]
    _ = frontier (A : Set X) := by
      simpa [h₂] using rfl

namespace Topology

theorem frontier_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (A : Set X) ⊆ closure (A : Set X) := by
  intro x hx
  exact hx.1

end Topology

namespace Topology

theorem SemiOpen.sUnion_closure_SemiOpen {X : Type*} [TopologicalSpace X]
    {𝒜 : Set (Set X)} (h𝒜 : ∀ S, S ∈ 𝒜 → SemiOpen S) :
    SemiOpen (closure (⋃₀ 𝒜)) := by
  -- First, the `sUnion` itself is semi‐open.
  have hUnion : SemiOpen (⋃₀ 𝒜) := SemiOpen.sUnion (𝒜 := 𝒜) h𝒜
  -- The closure of a semi‐open set is again semi‐open.
  simpa using SemiOpen.closure_SemiOpen (A := ⋃₀ 𝒜) hUnion

end Topology

theorem interior_eq_diff_closure_compl {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (A : Set X) = A \ closure ((A : Set X)ᶜ) := by
  classical
  -- We show the two inclusions separately.
  apply Set.Subset.antisymm
  · -- `⊆` direction: every interior point of `A` is outside `closure Aᶜ`.
    intro x hxInt
    have hxA : x ∈ (A : Set X) := interior_subset hxInt
    -- We claim that `x ∉ closure Aᶜ`.
    have hxNotCl : x ∉ closure ((A : Set X)ᶜ) := by
      intro hxCl
      -- `interior A` is an open neighbourhood of `x`.
      have hNonempty :
          ((interior (A : Set X)) ∩ (Aᶜ : Set X)).Nonempty :=
        (mem_closure_iff).1 hxCl (interior (A : Set X))
          isOpen_interior hxInt
      rcases hNonempty with ⟨y, hyInt, hyComp⟩
      have : y ∈ (A : Set X) := interior_subset hyInt
      exact (hyComp this).elim
    exact ⟨hxA, hxNotCl⟩
  · -- `⊇` direction: if `x ∈ A` and `x ∉ closure Aᶜ`, then `x` is interior to `A`.
    intro x hx
    rcases hx with ⟨hxA, hxNotCl⟩
    -- The open set `U = (closure Aᶜ)ᶜ` contains `x` and is contained in `A`.
    have hUopen : IsOpen ((closure ((A : Set X)ᶜ))ᶜ) :=
      (isClosed_closure : IsClosed (closure ((A : Set X)ᶜ))).isOpen_compl
    have hxU : x ∈ (closure ((A : Set X)ᶜ))ᶜ := hxNotCl
    have hUsubset : (closure ((A : Set X)ᶜ) : Set X)ᶜ ⊆ (A : Set X) := by
      intro y hyU
      by_contra hyNotA
      have : y ∈ closure ((A : Set X)ᶜ) :=
        subset_closure (show y ∈ (Aᶜ : Set X) from hyNotA)
      exact hyU this
    -- `U` is an open neighbourhood of `x` contained in `A`, hence `x ∈ interior A`.
    have hNhds : (closure ((A : Set X)ᶜ))ᶜ ∈ 𝓝 x :=
      hUopen.mem_nhds hxU
    have : (A : Set X) ∈ 𝓝 x :=
      Filter.mem_of_superset hNhds hUsubset
    exact (mem_interior_iff_mem_nhds).2 this

theorem IsClosed.frontier_eq_diff_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed (A : Set X)) :
    frontier (A : Set X) = A \ interior (A : Set X) := by
  simpa [frontier, hA.closure_eq]

namespace Topology

theorem PreOpen.isOpen_of_interior_closure_subset
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hPre : PreOpen (A : Set X))
    (hSubset : interior (closure (A : Set X)) ⊆ A) :
    IsOpen (A : Set X) := by
  -- `PreOpen` gives the inclusion `A ⊆ interior (closure A)`.
  have hIncl : (A : Set X) ⊆ interior (closure (A : Set X)) := hPre
  -- Hence we have equality of the two sets.
  have hEq : interior (closure (A : Set X)) = A :=
    Set.Subset.antisymm hSubset hIncl
  -- The interior of any set is open, so `A` is open.
  simpa [hEq] using (isOpen_interior : IsOpen (interior (closure (A : Set X))))

end Topology

namespace Topology

theorem AlphaOpen.sUnion_closure_SemiOpen {X : Type*} [TopologicalSpace X]
    {𝒜 : Set (Set X)} (h𝒜 : ∀ S, S ∈ 𝒜 → AlphaOpen S) :
    SemiOpen (closure (⋃₀ 𝒜)) := by
  -- Each α-open set is preopen.
  have hPre : ∀ S, S ∈ 𝒜 → PreOpen S := by
    intro S hS
    exact AlphaOpen.to_PreOpen (h𝒜 S hS)
  -- Apply the corresponding lemma for preopen sets.
  exact PreOpen.sUnion_closure_SemiOpen (𝒜 := 𝒜) hPre

end Topology

theorem interior_iInter_subset_iInter_interior {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {A : ι → Set X} :
    interior (⋂ i, A i : Set X) ⊆ ⋂ i, interior (A i) := by
  intro x hx
  -- We will show that `x` lies in the interior of every `A i`.
  have h : ∀ i, x ∈ interior (A i) := by
    intro i
    -- Use monotonicity of `interior` applied to the inclusion
    -- `⋂ i, A i ⊆ A i`.
    have hsubset : (⋂ j, A j : Set X) ⊆ A i := Set.iInter_subset _ _
    exact (interior_mono hsubset) hx
  -- Conclude the desired membership in the intersection of the interiors.
  exact Set.mem_iInter.2 h

namespace Topology

theorem AlphaOpen_iff_PreOpen_and_frontier_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    AlphaOpen (A : Set X) ↔
      (PreOpen (A : Set X) ∧
        frontier (A : Set X) ⊆ closure (interior (A : Set X))) := by
  -- Use the existing characterisations
  have h₁ := AlphaOpen_iff_PreOpen_and_SemiOpen (A := A)
  have h₂ := SemiOpen_iff_frontier_subset_closure_interior (A := A)
  -- Prove the two implications
  constructor
  · intro hAlpha
    -- Obtain `PreOpen A` and `SemiOpen A`
    rcases (h₁).1 hAlpha with ⟨hPre, hSemi⟩
    -- Convert `SemiOpen A` into the required frontier condition
    have hFront : frontier (A : Set X) ⊆ closure (interior (A : Set X)) :=
      (h₂).1 hSemi
    exact ⟨hPre, hFront⟩
  · rintro ⟨hPre, hFront⟩
    -- Turn the frontier condition into `SemiOpen A`
    have hSemi : SemiOpen (A : Set X) := (h₂).2 hFront
    -- Combine `PreOpen` and `SemiOpen` to obtain `AlphaOpen`
    exact (h₁).2 ⟨hPre, hSemi⟩

end Topology

theorem closure_compl_eq_compl_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure ((A : Set X)ᶜ) = (interior (A : Set X))ᶜ := by
  classical
  ext x
  constructor
  · intro hxCl
    by_cases hxInt : x ∈ interior (A : Set X)
    · -- If `x ∈ interior A` and `x ∈ closure Aᶜ`, obtain a contradiction.
      have hNonempty :
          ((interior (A : Set X)) ∩ ((A : Set X)ᶜ)).Nonempty :=
        (mem_closure_iff).1 hxCl (interior (A : Set X)) isOpen_interior hxInt
      rcases hNonempty with ⟨y, hyInt, hyNotA⟩
      have : y ∈ (A : Set X) := interior_subset hyInt
      exact (hyNotA this).elim
    · -- Otherwise `x ∉ interior A`, i.e. `x ∈ (interior A)ᶜ`.
      exact hxInt
  · intro hxNotInt
    -- Show that every neighbourhood of `x` meets `Aᶜ`.
    have h :
        ∀ V : Set X, IsOpen V → x ∈ V →
          ((V ∩ ((A : Set X)ᶜ)) : Set X).Nonempty := by
      intro V hVopen hxV
      by_contra hEmpty
      -- If `V ∩ Aᶜ` is empty, then `V ⊆ A`.
      have hVsubsetA : (V : Set X) ⊆ A := by
        intro y hyV
        by_contra hyNotA
        have : ((V ∩ ((A : Set X)ᶜ)) : Set X).Nonempty :=
          ⟨y, ⟨hyV, hyNotA⟩⟩
        exact hEmpty this
      -- Hence `x ∈ interior A`, contradicting `hxNotInt`.
      have hxIntA : x ∈ interior (A : Set X) := by
        have hVnhds : (V : Set X) ∈ 𝓝 x := hVopen.mem_nhds hxV
        have hAnhds : (A : Set X) ∈ 𝓝 x :=
          Filter.mem_of_superset hVnhds hVsubsetA
        exact (mem_interior_iff_mem_nhds).2 hAnhds
      exact hxNotInt hxIntA
    -- Translate the neighbourhood property into membership of the closure.
    exact (mem_closure_iff).2 h

namespace Topology

variable {X : Type*} [TopologicalSpace X]

theorem closure_interior_interior (A : Set X) :
    closure (interior (interior (A : Set X))) =
      closure (interior (A : Set X)) := by
  simpa [interior_interior]

end Topology

namespace Topology

theorem frontier_interior_eq_closureInterior_diff_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (interior (A : Set X)) =
      closure (interior (A : Set X)) \ interior (A : Set X) := by
  -- By definition, `frontier S = closure S \ interior S`.
  -- Applying this to `interior A` and using `interior (interior A) = interior A`
  -- yields the desired equality.
  simpa [frontier, interior_interior]

end Topology

namespace Topology

variable {X : Type*} [TopologicalSpace X]

/--
For any two sets `A` and `B`, the closure of the intersection of their interiors
is contained in the intersection of the closures of their interiors.
-/
theorem closure_inter_of_interiors_subset_inter_closures
    {A B : Set X} :
    closure (interior (A : Set X) ∩ interior (B : Set X)) ⊆
      closure (interior (A : Set X)) ∩ closure (interior (B : Set X)) := by
  intro x hx
  have h₁ :
      closure (interior (A : Set X) ∩ interior (B : Set X)) ⊆
        closure (interior (A : Set X)) :=
    closure_mono (Set.inter_subset_left : _ ⊆ interior A)
  have h₂ :
      closure (interior (A : Set X) ∩ interior (B : Set X)) ⊆
        closure (interior (B : Set X)) :=
    closure_mono (Set.inter_subset_right : _ ⊆ interior B)
  exact ⟨h₁ hx, h₂ hx⟩

end Topology



theorem IsClosed.frontier_subset
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed (A : Set X)) :
    frontier (A : Set X) ⊆ A := by
  intro x hx
  -- `hx.1` gives `x ∈ closure A`, which equals `A` because `A` is closed.
  have hxCl : x ∈ closure (A : Set X) := hx.1
  simpa [hA.closure_eq] using hxCl

namespace Topology

variable {X : Type*} [TopologicalSpace X]

theorem SemiOpen.closure_eq_closure_interior_union {A B : Set X}
    (hA : SemiOpen (A : Set X)) (hB : SemiOpen (B : Set X)) :
    closure (A ∪ B : Set X) = closure (interior (A ∪ B : Set X)) := by
  -- The union of two semi‐open sets is again semi‐open.
  have hUnion : SemiOpen (A ∪ B : Set X) :=
    SemiOpen.union (A := A) (B := B) hA hB
  -- Apply the characterisation of semi‐open sets to the union.
  exact SemiOpen.closure_eq_closure_interior (A := A ∪ B) hUnion

end Topology

theorem closure_interior_union_interior_closure_subset_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (A : Set X)) ∪ interior (closure (A : Set X)) ⊆
      closure (A : Set X) := by
  intro x hx
  cases hx with
  | inl hxClInt =>
      -- `closure (interior A) ⊆ closure A` by monotonicity of `closure`.
      have hSub :
          closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
        closure_mono (interior_subset : interior (A : Set X) ⊆ A)
      exact hSub hxClInt
  | inr hxIntCl =>
      -- `interior (closure A)` is contained in `closure A`.
      exact (interior_subset : interior (closure (A : Set X)) ⊆
        closure (A : Set X)) hxIntCl

theorem closure_inter_closure_subset_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ closure (B : Set X)) ⊆ closure (B : Set X) := by
  -- First, observe the obvious inclusion at the level of the sets themselves.
  have hSubset : (A ∩ closure (B : Set X) : Set X) ⊆ closure (B : Set X) := by
    intro x hx
    exact hx.2
  -- Apply `closure_mono`, which yields a map between the closures of the two sets.
  -- Note that the target is `closure (closure B) = closure B`.
  have h' :
      closure (A ∩ closure (B : Set X)) ⊆
        closure (closure (B : Set X)) :=
    closure_mono hSubset
  -- Finish by simplifying the double closure.
  simpa [closure_closure] using h'

theorem interior_compl_eq_compl_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior ((A : Set X)ᶜ) = (closure (A : Set X))ᶜ := by
  classical
  -- First, apply the lemma `closure_compl_eq_compl_interior` to `Aᶜ`.
  have h : closure (A : Set X) = (interior ((A : Set X)ᶜ))ᶜ := by
    simpa [Set.compl_compl] using
      (closure_compl_eq_compl_interior (A := (A : Set X)ᶜ))
  -- Take complements of both sides to relate the two interiors/closures.
  have h' : interior ((A : Set X)ᶜ) = (closure (A : Set X))ᶜ := by
    simpa using (congrArg (fun s : Set X => sᶜ) h).symm
  simpa using h'

namespace Topology

variable {X : Type*} [TopologicalSpace X]

/--
For any family of sets `A i`, the closure of their intersection is contained in
the intersection of their closures.
-/
theorem closure_iInter_subset_iInter_closure {ι : Sort*} {A : ι → Set X} :
    closure (⋂ i, A i : Set X) ⊆ ⋂ i, closure (A i) := by
  intro x hxCl
  -- For each index `i`, we show `x ∈ closure (A i)`.
  have h_mem : ∀ i, x ∈ closure (A i) := by
    intro i
    -- Since `⋂ i, A i ⊆ A i`, monotonicity of `closure` yields the claim.
    have h_subset : (⋂ j, A j : Set X) ⊆ A i := Set.iInter_subset _ _
    have h_closure_subset :
        closure (⋂ j, A j : Set X) ⊆ closure (A i) :=
      closure_mono h_subset
    exact h_closure_subset hxCl
  -- Assemble the facts into membership of the intersection of closures.
  exact Set.mem_iInter.2 h_mem

end Topology

theorem Topology.SemiOpen.closure_interior_eq_set_union_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.SemiOpen (A : Set X)) :
    closure (interior (A : Set X)) =
      (A : Set X) ∪ frontier (A : Set X) := by
  -- Step 1: identify `closure (interior A)` with `closure A`.
  have hCl :
      closure (interior (A : Set X)) = closure (A : Set X) := by
    symm
    exact Topology.SemiOpen.closure_eq_closure_interior (A := A) hA
  -- Step 2: rewrite `closure A` using the general decomposition.
  have hDecomp :
      closure (A : Set X) =
        interior (A : Set X) ∪ frontier (A : Set X) :=
    closure_eq_interior_union_frontier (A := A)
  -- Substitute and simplify.
  have h₁ :
      closure (interior (A : Set X)) ⊆
        (A : Set X) ∪ frontier (A : Set X) := by
    -- `interior A ⊆ A`, hence `interior A ∪ frontier A ⊆ A ∪ frontier A`.
    have : (interior (A : Set X) ∪ frontier (A : Set X)) ⊆
        (A : Set X) ∪ frontier (A : Set X) := by
      intro x hx
      cases hx with
      | inl hxInt => exact Or.inl (interior_subset hxInt)
      | inr hxFr  => exact Or.inr hxFr
    simpa [hCl, hDecomp] using this
  have h₂ :
      (A : Set X) ∪ frontier (A : Set X) ⊆
        closure (interior (A : Set X)) := by
    intro x hx
    cases hx with
    | inl hxA =>
        exact (Topology.SemiOpen.subset_closure_interior (A := A) hA) hxA
    | inr hxFr =>
        exact
          (Topology.SemiOpen.frontier_subset_closure_interior (A := A) hA) hxFr
  exact Set.Subset.antisymm h₁ h₂

theorem Topology.SemiOpen_iff_frontier_eq_frontier_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    SemiOpen (A : Set X) ↔
      frontier (A : Set X) = frontier (interior (A : Set X)) := by
  -- Forward direction: a semi-open set has equal frontiers
  -- by an existing lemma.
  constructor
  · intro hSemi
    exact SemiOpen.frontier_eq_frontier_interior (A := A) hSemi
  · intro hEq
    -- We will prove the frontier inclusion required for semi-openness
    -- and then apply the known characterisation.
    have hSubset : frontier (A : Set X) ⊆ closure (interior (A : Set X)) := by
      intro x hxFront
      -- Rewrite membership using the assumed equality of frontiers.
      have hxFrontInt : x ∈ frontier (interior (A : Set X)) := by
        simpa [hEq] using hxFront
      -- Any point in a frontier lies in the corresponding closure.
      exact hxFrontInt.1
    -- Conclude `SemiOpen A` from the frontier inclusion.
    exact
      (SemiOpen_iff_frontier_subset_closure_interior (A := A)).2 hSubset

namespace Topology

theorem frontier_frontier_subset_frontier {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    frontier (frontier (A : Set X)) ⊆ frontier (A : Set X) := by
  intro x hx
  -- `hx` yields `x ∈ closure (frontier A)`.
  have hx_cl : x ∈ closure (frontier (A : Set X)) := hx.1
  -- Since `frontier A` is closed, its closure is itself.
  have hClosed : IsClosed (frontier (A : Set X)) := isClosed_frontier
  have hEq : closure (frontier (A : Set X)) = frontier (A : Set X) :=
    hClosed.closure_eq
  -- Rewriting with this equality gives the desired membership.
  simpa [hEq] using hx_cl

end Topology

theorem IsClosed.preopen_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hAclosed : IsClosed (A : Set X)) (hApre : Topology.PreOpen (A : Set X)) :
    IsOpen (A : Set X) := by
  exact (IsClosed.preopen_iff_open (A := A) hAclosed).1 hApre

theorem interior_closure_iInter_subset_iInter_interior_closure
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    interior (closure (⋂ i, A i : Set X)) ⊆ ⋂ i, interior (closure (A i)) := by
  intro x hx
  -- For each index `i`, relate the two closures via monotonicity.
  have hInt :
      ∀ i, interior (closure (⋂ j, A j : Set X)) ⊆
        interior (closure (A i)) := by
    intro i
    -- The inclusion `⋂ j, A j ⊆ A i` yields the desired relation.
    have hSubset : (⋂ j, A j : Set X) ⊆ A i := Set.iInter_subset _ _
    have hClSubset : closure (⋂ j, A j : Set X) ⊆ closure (A i) :=
      closure_mono hSubset
    exact interior_mono hClSubset
  -- Assemble the membership in every component of the intersection.
  exact Set.mem_iInter.2 (fun i => (hInt i) hx)

theorem frontier_eq_closure_diff_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    frontier (A : Set X) =
      closure (A : Set X) \ interior (A : Set X) := by
  rfl

theorem interior_inter_frontier_eq_empty {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (A : Set X) ∩ frontier (A : Set X) = (∅ : Set X) := by
  apply Set.eq_empty_iff_forall_not_mem.2
  intro x hx
  rcases hx with ⟨hxInt, hxFront⟩
  exact hxFront.2 hxInt

theorem Continuous.closure_preimage_subset {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) (S : Set Y) :
    closure (f ⁻¹' S) ⊆ f ⁻¹' closure S := by
  -- `S` is contained in its closure, hence the same holds for the preimages.
  have hSubset : (f ⁻¹' S : Set X) ⊆ f ⁻¹' closure S := by
    intro x hx
    exact subset_closure hx
  -- The preimage of a closed set under a continuous map is closed.
  have hClosed : IsClosed (f ⁻¹' closure S) :=
    (isClosed_closure : IsClosed (closure S)).preimage hf
  -- Apply the minimality property of the closure.
  exact closure_minimal hSubset hClosed

theorem Topology.SemiOpen.diff_closureInterior_subset_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.SemiOpen (A : Set X)) :
    closure (interior (A : Set X)) \ A ⊆ frontier (A : Set X) := by
  intro x hx
  -- Decompose the hypothesis.
  have hxClInt : x ∈ closure (interior (A : Set X)) := hx.1
  have hxNotA  : x ∉ (A : Set X) := hx.2
  -- A semi-open set satisfies `closure A = closure (interior A)`.
  have hEq := Topology.SemiOpen.closure_eq_closure_interior (A := A) hA
  -- Transport membership along this equality.
  have hxClA : x ∈ closure (A : Set X) := by
    simpa [hEq] using hxClInt
  -- Since `interior A ⊆ A`, `x ∉ A` implies `x ∉ interior A`.
  have hxNotInt : x ∉ interior (A : Set X) := by
    intro hxInt
    exact hxNotA (interior_subset hxInt)
  -- Assemble the two facts into membership of the frontier.
  exact ⟨hxClA, hxNotInt⟩



namespace Topology

theorem SemiOpen.nonempty_iff_closure_interior_nonempty {X : Type*}
    [TopologicalSpace X] {A : Set X} (hA : SemiOpen (A : Set X)) :
    (A : Set X).Nonempty ↔ (closure (interior (A : Set X))).Nonempty := by
  classical
  constructor
  · intro hANon
    rcases hANon with ⟨x, hxA⟩
    exact ⟨x, hA hxA⟩
  · intro hClIntNon
    by_cases hANon : (A : Set X).Nonempty
    · exact hANon
    · have hAempty : (A : Set X) = (∅ : Set X) := by
        apply Set.eq_empty_iff_forall_not_mem.2
        intro x hx
        have : (A : Set X).Nonempty := ⟨x, hx⟩
        exact (hANon this).elim
      have hIntEmpty : interior (A : Set X) = (∅ : Set X) := by
        simpa [hAempty, interior_empty] using rfl
      have hClIntEmpty : closure (interior (A : Set X)) = (∅ : Set X) := by
        simpa [hIntEmpty, closure_empty]
      have : (closure (interior (A : Set X))).Nonempty := hClIntNon
      simpa [hClIntEmpty] using this

end Topology

theorem frontier_inter_subset_inter_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    frontier (A ∩ B : Set X) ⊆
      closure (A : Set X) ∩ closure (B : Set X) := by
  intro x hx
  have hxCl : x ∈ closure (A ∩ B : Set X) := hx.1
  have hxClA : x ∈ closure (A : Set X) :=
    (closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)) hxCl
  have hxClB : x ∈ closure (B : Set X) :=
    (closure_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)) hxCl
  exact ⟨hxClA, hxClB⟩

namespace Topology

theorem SemiOpen.frontier_eq_closure_diff_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} (hA : SemiOpen (A : Set X)) :
    frontier (A : Set X) = closure (A : Set X) \ interior (A : Set X) := by
  -- Start from the characterisation of the frontier for semi-open sets.
  have h₁ :
      frontier (A : Set X) =
        closure (interior (A : Set X)) \ interior (A : Set X) :=
    SemiOpen.frontier_eq_closureInterior_diff_interior (A := A) hA
  -- For semi-open sets we have `closure A = closure (interior A)`.
  have h₂ :
      closure (interior (A : Set X)) = closure (A : Set X) :=
    (SemiOpen.closure_eq_closure_interior (A := A) hA).symm
  -- Rewrite the result using this equality.
  simpa [h₂] using h₁

end Topology



namespace Topology

theorem diff_closureInterior_subset_frontier {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior (A : Set X)) \ (A : Set X) ⊆ frontier (A : Set X) := by
  intro x hx
  -- `hx` gives `x ∈ closure (interior A)` and `x ∉ A`.
  have hx_cl_int : x ∈ closure (interior (A : Set X)) := hx.1
  have hx_notA : x ∉ (A : Set X) := hx.2
  -- Since `interior A ⊆ A`, we get `closure (interior A) ⊆ closure A`.
  have h_subset : closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
    closure_mono (interior_subset : interior (A : Set X) ⊆ A)
  -- Hence `x ∈ closure A`.
  have hx_clA : x ∈ closure (A : Set X) := h_subset hx_cl_int
  -- From `x ∉ A` and `interior A ⊆ A`, infer `x ∉ interior A`.
  have hx_not_int : x ∉ interior (A : Set X) := by
    intro hx_int
    exact hx_notA (interior_subset hx_int)
  -- Combine the two facts to obtain membership in the frontier.
  exact ⟨hx_clA, hx_not_int⟩

end Topology



theorem closure_compl_eq_interior_compl_union_frontier
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure ((A : Set X)ᶜ) =
      interior ((A : Set X)ᶜ) ∪ frontier (A : Set X) := by
  -- Apply the decomposition of a closure into its interior and frontier
  -- to the complement set `Aᶜ`, and then rewrite the frontier of a
  -- complement as the frontier of the original set.
  simpa [frontier_compl] using
    (closure_eq_interior_union_frontier (A := (Aᶜ : Set X)))

theorem closure_inter_subset_closure_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A : Set X) ∩ closure (B : Set X) ⊆
      closure (A ∪ B : Set X) := by
  intro x hx
  -- From the intersection we obtain `x ∈ closure A`.
  have hxA : x ∈ closure (A : Set X) := hx.1
  -- Monotonicity of `closure` applied to `A ⊆ A ∪ B`.
  have hIncl : closure (A : Set X) ⊆ closure (A ∪ B : Set X) :=
    closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
  exact hIncl hxA

theorem closure_diff_closure_subset_closure_diff {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A : Set X) \ closure (B : Set X) ⊆ closure (A \ B : Set X) := by
  intro x hx
  -- `x` lies in `closure A` but not in `closure B`.
  have hxClA : x ∈ closure (A : Set X) := hx.1
  have hxNotClB : x ∉ closure (B : Set X) := hx.2
  -- The complement of `closure B` is an open neighbourhood of `x`.
  have hOpenCompl : IsOpen ((closure (B : Set X))ᶜ) :=
    (isClosed_closure : IsClosed (closure (B : Set X))).isOpen_compl
  -- We will prove that every open neighbourhood of `x` meets `A \ B`.
  apply (mem_closure_iff).2
  intro S hSopen hxS
  -- Refine the neighbourhood by intersecting with the open complement of `closure B`.
  let W : Set X := S ∩ (closure (B : Set X))ᶜ
  have hWopen : IsOpen W := hSopen.inter hOpenCompl
  have hxW : x ∈ W := by
    dsimp [W]
    exact ⟨hxS, hxNotClB⟩
  -- Since `x ∈ closure A`, the neighbourhood `W` meets `A`.
  have hNonempty : ((W ∩ A : Set X)).Nonempty :=
    (mem_closure_iff).1 hxClA W hWopen hxW
  -- Extract a witness in `S ∩ (A \ B)`.
  rcases hNonempty with ⟨y, hyW, hyA⟩
  have hyS : y ∈ S := hyW.1
  have hyNotClB : y ∈ (closure (B : Set X))ᶜ := hyW.2
  -- From `hyNotClB` deduce `y ∉ B`.
  have hyNotB : y ∉ B := by
    intro hyB
    exact hyNotClB (subset_closure hyB)
  -- Assemble the required witness.
  exact
    ⟨y, by
      have : y ∈ A \ B := ⟨hyA, hyNotB⟩
      exact ⟨hyS, this⟩⟩

theorem Continuous.preimage_AlphaOpen
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : Continuous f) {V : Set Y} (hV : IsOpen V) :
    Topology.AlphaOpen (f ⁻¹' V) := by
  -- The preimage of an open set under a continuous map is open.
  have hOpen : IsOpen (f ⁻¹' V) := hV.preimage hf
  -- Any open set is α-open.
  simpa using IsOpen.to_AlphaOpen hOpen



theorem closure_inter_of_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed (A : Set X)) (hB : IsClosed (B : Set X)) :
    closure (A ∩ B : Set X) = A ∩ B := by
  have hClosed : IsClosed (A ∩ B : Set X) := hA.inter hB
  simpa using hClosed.closure_eq

theorem IsClosed.frontier_eq_of_empty_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X))
    (hInt : interior (A : Set X) = (∅ : Set X)) :
    frontier (A : Set X) = A := by
  -- For a closed set, `frontier A = A \ interior A`.
  have h₀ := IsClosed.frontier_eq_diff_interior (A := A) hA
  -- Substitute the assumption `interior A = ∅`.
  simpa [hInt, Set.diff_empty] using h₀

theorem interior_diff_subset_left {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A \ B : Set X) ⊆ interior (A : Set X) := by
  exact interior_mono (Set.diff_subset : (A \ B : Set X) ⊆ A)

theorem interior_closure_inter_closure_subset_interiors
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A : Set X) ∩ closure (B : Set X)) ⊆
      interior (closure (A : Set X)) ∩ interior (closure (B : Set X)) := by
  -- Apply the general inclusion
  -- `interior (S ∩ T) ⊆ interior S ∩ interior T`
  -- to `S = closure A` and `T = closure B`.
  simpa using
    (interior_inter_subset_inter_interior
      (A := closure (A : Set X)) (B := closure (B : Set X)))



theorem Topology.AlphaOpen.frontier_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.AlphaOpen (A : Set X)) :
    frontier (A : Set X) ⊆ closure (interior (closure (A : Set X))) := by
  intro x hx
  -- From `AlphaOpen`, obtain the basic frontier inclusion.
  have hx₁ : x ∈ closure (interior (A : Set X)) :=
    (Topology.AlphaOpen.frontier_subset_closure_interior (A := A) hA) hx
  -- `interior A` is contained in `interior (closure A)`.
  have hIntSubset :
      interior (A : Set X) ⊆ interior (closure (A : Set X)) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  -- Taking closures preserves inclusions.
  have hClSubset :
      closure (interior (A : Set X)) ⊆
        closure (interior (closure (A : Set X))) :=
    closure_mono hIntSubset
  exact hClSubset hx₁



theorem Continuous.preimage_SemiOpen
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : Continuous f) {V : Set Y} (hV : IsOpen V) :
    Topology.SemiOpen (f ⁻¹' V) := by
  -- The preimage of an open set under a continuous map is open.
  have hOpen : IsOpen (f ⁻¹' V) := hV.preimage hf
  -- Every open set is semi‐open.
  simpa using (IsOpen.to_SemiOpen hOpen)

theorem closure_union_of_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed (A : Set X)) (hB : IsClosed (B : Set X)) :
    closure (A ∪ B : Set X) = A ∪ B := by
  have hClosed : IsClosed (A ∪ B : Set X) := hA.union hB
  simpa using hClosed.closure_eq

namespace Topology

theorem iUnionInterior_subset_interior_iUnion {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {A : ι → Set X} :
    (⋃ i, interior (A i) : Set X) ⊆ interior (⋃ i, A i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxInt⟩
  -- `A i` is contained in the union, hence so is its interior.
  have hSub : interior (A i) ⊆ interior (⋃ j, A j) := by
    apply interior_mono
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  exact hSub hxInt

end Topology

namespace Topology

variable {X : Type*} [TopologicalSpace X]

/--  
If every set in a family is open, then the interior of the union is the union  
itself.  
-/
theorem interior_iUnion_of_open {ι : Sort*} {A : ι → Set X}
    (hA : ∀ i, IsOpen (A i)) :
    interior (⋃ i, A i : Set X) = ⋃ i, A i := by
  have hOpen : IsOpen (⋃ i, A i : Set X) := isOpen_iUnion hA
  simpa using hOpen.interior_eq

end Topology

theorem interior_closure_inter_closure_eq {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (closure (A : Set X)) ∩ closure (A : Set X) =
      interior (closure (A : Set X)) := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    exact ⟨hx, interior_subset hx⟩

namespace Topology

theorem SemiOpen.union_alpha {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : SemiOpen (A : Set X)) (hB : AlphaOpen (B : Set X)) :
    SemiOpen (A ∪ B : Set X) := by
  -- Turn the α-open set `B` into a semi-open set.
  have hBsemi : SemiOpen (B : Set X) := AlphaOpen.to_SemiOpen hB
  -- The union of two semi-open sets is semi-open.
  exact (SemiOpen.union (A := A) (B := B) hA hBsemi)

end Topology

theorem closure_diff_subset_frontier {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) \ A ⊆ frontier (A : Set X) := by
  intro x hx
  -- Decompose the hypothesis: `x ∈ closure A` and `x ∉ A`.
  have hxCl : x ∈ closure (A : Set X) := hx.1
  have hxNotA : x ∉ (A : Set X) := hx.2
  -- Since `interior A ⊆ A`, the second condition implies
  -- `x ∉ interior A`.
  have hxNotInt : x ∉ interior (A : Set X) := by
    intro hxInt
    exact hxNotA (interior_subset hxInt)
  -- Combine the two facts to obtain membership in the frontier.
  exact ⟨hxCl, hxNotInt⟩

theorem IsOpen.union_PreOpen {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    Topology.PreOpen ((A ∪ B : Set X)) := by
  simpa using IsOpen.to_PreOpen (hA.union hB)

theorem closure_diff_subset_closure_minus_interior {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A \ B : Set X) ⊆ closure (A : Set X) \ interior (B : Set X) := by
  intro x hxCl
  -- First, `x` lies in `closure A`, since `A \ B ⊆ A`.
  have hClA : x ∈ closure (A : Set X) :=
    (closure_mono (Set.diff_subset : (A \ B : Set X) ⊆ A)) hxCl
  -- Next, we show that `x ∉ interior B`.
  have hNotIntB : x ∉ interior (B : Set X) := by
    intro hxIntB
    -- Use the neighbourhood characterisation of the closure.
    have hNonempty :=
      (mem_closure_iff).1 hxCl (interior (B : Set X))
        isOpen_interior hxIntB
    rcases hNonempty with ⟨y, hyIntB, hyInDiff⟩
    have hyB  : y ∈ B := interior_subset hyIntB
    exact hyInDiff.2 hyB
  exact ⟨hClA, hNotIntB⟩

theorem Topology.PreOpen.of_open_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hOpen : IsOpen (closure (A : Set X))) :
    Topology.PreOpen (A : Set X) := by
  -- Unfold the definition of `PreOpen`.
  unfold Topology.PreOpen
  intro x hxA
  -- Any point of `A` is, by definition, in `closure A`.
  have hxCl : x ∈ closure (A : Set X) := subset_closure hxA
  -- Since `closure A` is open, its interior coincides with itself.
  have hIntEq : interior (closure (A : Set X)) = closure (A : Set X) :=
    hOpen.interior_eq
  -- Re-express the goal using this equality.
  simpa [hIntEq] using hxCl

theorem closure_union_interiors_subset_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X) ∪ interior (B : Set X)) ⊆
      closure (A ∪ B : Set X) := by
  -- The union of the two interiors is contained in `A ∪ B`.
  have hSubset :
      (interior (A : Set X) ∪ interior (B : Set X) : Set X) ⊆
        A ∪ B := by
    intro x hx
    cases hx with
    | inl hA =>
        exact Or.inl (interior_subset hA)
    | inr hB =>
        exact Or.inr (interior_subset hB)
  -- Taking closures preserves inclusions.
  exact closure_mono hSubset

theorem closure_inter_interior_compl_eq_empty {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (A : Set X) ∩ interior ((A : Set X)ᶜ) = (∅ : Set X) := by
  -- First, show that the intersection is contained in `∅`.
  have hsubset :
      closure (A : Set X) ∩ interior ((A : Set X)ᶜ) ⊆ (∅ : Set X) := by
    -- Use a previously established inclusion with `B = Aᶜ`.
    have h :=
      closure_inter_interior_subset_left (A := A) (B := (Aᶜ : Set X))
    -- Note that `A ∩ Aᶜ = ∅`, and `closure ∅ = ∅`.
    simpa [Set.inter_compl_self, closure_empty] using h
  -- Since `∅` is contained in any set, the reverse inclusion is trivial.
  apply Set.Subset.antisymm hsubset
  intro x hx
  cases hx

theorem closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (A : Set X)) ⊆
      closure (interior (closure (A : Set X))) := by
  -- `A ⊆ closure A`
  have h₁ : (A : Set X) ⊆ closure (A : Set X) := subset_closure
  -- Taking interiors preserves inclusions.
  have h₂ : interior (A : Set X) ⊆ interior (closure (A : Set X)) :=
    interior_mono h₁
  -- Taking closures once more yields the desired inclusion.
  exact closure_mono h₂

namespace Topology

theorem AlphaOpen.inter_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : AlphaOpen (A : Set X)) :
    AlphaOpen (A ∩ interior (A : Set X)) := by
  have hOpen : IsOpen (interior (A : Set X)) := isOpen_interior
  simpa using AlphaOpen.inter_open (A := A) (U := interior A) hA hOpen

end Topology

namespace Topology

theorem SemiOpen.inter_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : SemiOpen (A : Set X)) :
    SemiOpen (A ∩ interior (closure (A : Set X))) := by
  have hOpen : IsOpen (interior (closure (A : Set X))) := isOpen_interior
  simpa using
    SemiOpen.inter_open (A := A) (U := interior (closure (A : Set X))) hA hOpen

end Topology



namespace Topology

variable {X : Type*} [TopologicalSpace X]

theorem frontier_subset_closure_of_subset {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    frontier (A : Set X) ⊆ closure (B : Set X) := by
  intro x hx
  -- `hx.1` gives `x ∈ closure A`
  have hxClA : x ∈ closure (A : Set X) := hx.1
  -- Apply monotonicity of `closure` to the inclusion `A ⊆ B`
  have hClSubset : closure (A : Set X) ⊆ closure (B : Set X) :=
    closure_mono hAB
  exact hClSubset hxClA

end Topology

theorem Topology.AlphaOpen.closure_interior_eq_set_union_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.AlphaOpen (A : Set X)) :
    closure (interior (A : Set X)) =
      (A : Set X) ∪ frontier (A : Set X) := by
  -- An α-open set is semi-open, hence we can reuse the semi-open lemma.
  have hSemi : Topology.SemiOpen (A : Set X) :=
    Topology.AlphaOpen.to_SemiOpen hA
  simpa using
    Topology.SemiOpen.closure_interior_eq_set_union_frontier
      (A := A) hSemi





theorem Topology.interior_closure_interior_closure_interior_eq_interior_closure_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (A : Set X))))) =
      interior (closure (interior (A : Set X))) := by
  -- First, recall the equality of closures established earlier.
  have h :=
    Topology.closure_interior_closure_interior_eq_closure_interior (A := A)
  -- Apply `interior` to both sides of that equality.
  simpa using congrArg (fun S : Set X => interior S) h

theorem frontier_closure_subset_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    frontier (closure (A : Set X)) ⊆ closure (A : Set X) := by
  intro x hx
  -- By definition `x ∈ frontier (closure A)` means
  -- `x ∈ closure (closure A)` and `x ∉ interior (closure A)`.
  -- The first component already gives the desired conclusion.
  simpa [closure_closure] using hx.1

theorem interior_closure_diff_subset_frontier {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (closure (A : Set X)) \ (A : Set X) ⊆ frontier (A : Set X) := by
  intro x hx
  -- Decompose the membership in the set difference.
  have hxInt : x ∈ interior (closure (A : Set X)) := hx.1
  have hxNotA : x ∉ (A : Set X) := hx.2
  -- From the interior we pass to the closure.
  have hxCl : x ∈ closure (A : Set X) := interior_subset hxInt
  -- Since `interior A ⊆ A`, the negation of `x ∈ A` implies
  -- `x ∉ interior A`.
  have hxNotIntA : x ∉ interior (A : Set X) := by
    intro hInt
    exact hxNotA (interior_subset hInt)
  -- Assemble the conditions for membership in the frontier.
  exact ⟨hxCl, hxNotIntA⟩

theorem frontier_union_subset_union_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier (A ∪ B : Set X) ⊆
      closure (A : Set X) ∪ closure (B : Set X) := by
  intro x hx
  -- From `hx` we obtain `x ∈ closure (A ∪ B)`.
  have hxCl : x ∈ closure (A ∪ B : Set X) := hx.1
  -- Apply the inclusion established for closures of unions.
  have hIncl :
      closure (A ∪ B : Set X) ⊆
        closure (A : Set X) ∪ closure (B : Set X) :=
    closure_union_subset_union_closure
  exact hIncl hxCl

theorem interior_diff_closure_eq {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A \ closure (B : Set X) : Set X) =
      interior (A : Set X) \ closure (B : Set X) := by
  -- `closure B` is always a closed set.
  have hClosed : IsClosed (closure (B : Set X)) := isClosed_closure
  -- Apply the previously established lemma for the case of a closed set.
  simpa using
    (interior_diff_closed_eq (A := A) (B := closure (B : Set X)) hClosed)

theorem closure_inter_interior_subset_inter_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ interior (B : Set X)) ⊆
      closure (A : Set X) ∩ closure (B : Set X) := by
  intro x hx
  -- First component: `x ∈ closure A`.
  have hxA : x ∈ closure (A : Set X) := by
    have hSubset : (A ∩ interior (B : Set X) : Set X) ⊆ A := by
      intro y hy; exact hy.1
    exact (closure_mono hSubset) hx
  -- Second component: `x ∈ closure B`.
  have hxB : x ∈ closure (B : Set X) := by
    have hSubset : (A ∩ interior (B : Set X) : Set X) ⊆ B := by
      intro y hy; exact interior_subset hy.2
    exact (closure_mono hSubset) hx
  -- Assemble the pair.
  exact ⟨hxA, hxB⟩

theorem closure_eq_interior_closure_union_frontier
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (A : Set X) =
      interior (closure (A : Set X)) ∪ frontier (closure (A : Set X)) := by
  -- Apply the general decomposition lemma to the set `closure A`.
  simpa [closure_closure] using
    (closure_eq_interior_union_frontier
        (A := closure (A : Set X)))

theorem closure_interior_closure_intersection_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (closure (A : Set X) ∩ closure (B : Set X))) ⊆
      closure (interior (closure (A : Set X))) ∩
        closure (interior (closure (B : Set X))) := by
  intro x hx
  have h₁ :
      closure (interior (closure (A : Set X) ∩ closure (B : Set X))) ⊆
        closure (interior (closure (A : Set X))) := by
    -- `closure A ∩ closure B ⊆ closure A`
    have hSubset :
        interior (closure (A : Set X) ∩ closure B) ⊆
          interior (closure (A : Set X)) := by
      apply interior_mono
      exact Set.inter_subset_left
    -- Taking closures preserves inclusions.
    exact closure_mono hSubset
  have h₂ :
      closure (interior (closure (A : Set X) ∩ closure (B : Set X))) ⊆
        closure (interior (closure (B : Set X))) := by
    -- `closure A ∩ closure B ⊆ closure B`
    have hSubset :
        interior (closure (A : Set X) ∩ closure B) ⊆
          interior (closure (B : Set X)) := by
      apply interior_mono
      exact Set.inter_subset_right
    exact closure_mono hSubset
  exact ⟨h₁ hx, h₂ hx⟩

theorem interior_closure_eq_self_iff_isOpen_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (closure (A : Set X)) = closure (A : Set X) ↔
      IsOpen (closure (A : Set X)) := by
  constructor
  · intro hEq
    -- The interior of any set is open, so the equality forces `closure A` to be open.
    simpa [hEq] using
      (isOpen_interior : IsOpen (interior (closure (A : Set X))))
  · intro hOpen
    -- For an open set, the interior is the set itself.
    simpa using hOpen.interior_eq

theorem Topology.SemiOpen.union_frontier_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.SemiOpen (A : Set X)) :
    (A : Set X) ∪ frontier (A : Set X) = closure (A : Set X) := by
  calc
    (A : Set X) ∪ frontier (A : Set X)
        = closure (interior (A : Set X)) := by
          simpa using
            (Topology.SemiOpen.closure_interior_eq_set_union_frontier
                (A := A) hA).symm
    _ = closure (A : Set X) := by
          simpa
            [Topology.SemiOpen.closure_eq_closure_interior (A := A) hA]

theorem Topology.PreOpen.of_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.PreOpen (closure (A : Set X))) :
    Topology.PreOpen (A : Set X) := by
  -- Unfold the definition of `PreOpen`.
  unfold Topology.PreOpen at h ⊢
  intro x hxA
  -- Any point of `A` lies in its closure.
  have hxClA : x ∈ closure (A : Set X) := subset_closure hxA
  -- Apply the hypothesis to upgrade membership to the interior of the
  -- closure of `closure A`, then simplify the double closure.
  have : x ∈ interior (closure (closure (A : Set X))) := h hxClA
  simpa [closure_closure] using this

theorem frontier_closure_eq_closure_diff_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    frontier (closure (A : Set X)) =
      closure (A : Set X) \ interior (closure (A : Set X)) := by
  simpa [closure_closure] using
    (frontier_eq_closure_diff_interior
      (A := closure (A : Set X)))

theorem closureInterior_inter_interior_compl_eq_empty
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (A : Set X)) ∩ interior ((A : Set X)ᶜ) = (∅ : Set X) := by
  apply Set.eq_empty_iff_forall_not_mem.2
  intro x hx
  -- Decompose the membership condition.
  have hxClInt : x ∈ closure (interior (A : Set X)) := hx.1
  have hxIntCompl : x ∈ interior ((A : Set X)ᶜ) := hx.2
  -- Use the neighbourhood characterisation of the closure.
  have hNonempty :
      ((interior ((A : Set X)ᶜ)) ∩ interior (A : Set X)).Nonempty :=
    (mem_closure_iff).1 hxClInt _ isOpen_interior hxIntCompl
  -- Obtain a witness in the (impossible) intersection.
  rcases hNonempty with ⟨y, ⟨hyIntCompl, hyIntA⟩⟩
  have hyNotA : y ∈ (A : Set X)ᶜ := interior_subset hyIntCompl
  have hyA    : y ∈ (A : Set X)   := interior_subset hyIntA
  exact hyNotA hyA

theorem interior_closure_empty {X : Type*} [TopologicalSpace X] :
    interior (closure (∅ : Set X)) = (∅ : Set X) := by
  simpa [closure_empty, interior_empty]

theorem closure_diff_interiorClosure_subset_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) \ interior (closure (A : Set X)) ⊆
      frontier (A : Set X) := by
  intro x hx
  -- Decompose the membership in the set difference.
  have hxCl : x ∈ closure (A : Set X) := hx.1
  have hxNotIntCl : x ∉ interior (closure (A : Set X)) := hx.2
  -- Since `interior A ⊆ interior (closure A)`, the second condition implies
  -- that `x ∉ interior A`.
  have hxNotIntA : x ∉ interior (A : Set X) := by
    intro hxIntA
    have hIncl :
        interior (A : Set X) ⊆ interior (closure (A : Set X)) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure (A : Set X))
    exact hxNotIntCl (hIncl hxIntA)
  -- Assemble the facts to obtain membership of the frontier.
  exact ⟨hxCl, hxNotIntA⟩

theorem frontier_interior_closure_subset_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (interior (closure (A : Set X))) ⊆ frontier (A : Set X) := by
  intro x hx
  -- Decompose the membership in the frontier of `interior (closure A)`.
  have hxClInt : x ∈ closure (interior (closure (A : Set X))) := hx.1
  have hxNotIntInt : x ∉ interior (interior (closure (A : Set X))) := hx.2
  -- The first component upgrades to membership in `closure A`.
  have hSubset :
      closure (interior (closure (A : Set X))) ⊆ closure (A : Set X) := by
    simpa using
      (Topology.closure_interior_subset_closure
        (A := closure (A : Set X)))
  have hxClA : x ∈ closure (A : Set X) := hSubset hxClInt
  -- Simplify the non‐interior condition.
  have hxNotIntCl : x ∉ interior (closure (A : Set X)) := by
    simpa [interior_interior] using hxNotIntInt
  -- Since `interior A ⊆ interior (closure A)`, we deduce `x ∉ interior A`.
  have hIntSubset :
      interior (A : Set X) ⊆ interior (closure (A : Set X)) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure (A : Set X))
  have hxNotIntA : x ∉ interior (A : Set X) := by
    intro hxIntA
    exact hxNotIntCl (hIntSubset hxIntA)
  -- Assemble the two facts to obtain membership in the desired frontier.
  exact ⟨hxClA, hxNotIntA⟩

theorem closure_interior_union_frontier_eq_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (A : Set X)) ∪ frontier (A : Set X) =
      closure (A : Set X) := by
  ext x
  constructor
  · intro hx
    cases hx with
    | inl hxi =>
        -- `closure (interior A)` is contained in `closure A`
        exact (closure_mono (interior_subset : interior (A : Set X) ⊆ A)) hxi
    | inr hxFront =>
        -- By definition, the frontier is contained in the closure
        exact hxFront.1
  · intro hxCl
    by_cases hxInt : x ∈ interior (A : Set X)
    · -- Points of `interior A` belong to `closure (interior A)`
      have : x ∈ closure (interior (A : Set X)) := subset_closure hxInt
      exact Or.inl this
    · -- Otherwise they lie in the frontier
      have : x ∈ frontier (A : Set X) := ⟨hxCl, hxInt⟩
      exact Or.inr this

theorem frontier_frontier_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (frontier (A : Set X)) ⊆ closure (A : Set X) := by
  intro x hx
  have hxFront : x ∈ frontier (A : Set X) :=
    (Topology.frontier_frontier_subset_frontier (A := A)) hx
  exact hxFront.1

namespace Topology

theorem closure_iInter_of_closed {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {A : ι → Set X} (hA : ∀ i, IsClosed (A i)) :
    closure (⋂ i, A i : Set X) = ⋂ i, A i := by
  -- The intersection of closed sets is itself closed.
  have hClosed : IsClosed (⋂ i, A i : Set X) :=
    isClosed_iInter (fun i => hA i)
  -- Taking the closure of a closed set leaves it unchanged.
  simpa using hClosed.closure_eq

end Topology

theorem interior_closure_interior_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (closure (interior (A : Set X))) ⊆ closure (A : Set X) := by
  intro x hx
  -- From `hx` we get `x ∈ closure (interior A)`.
  have hx_cl : x ∈ closure (interior (A : Set X)) := interior_subset hx
  -- Use the previously established inclusion
  -- `closure (interior A) ⊆ closure A`.
  have h_subset :
      closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
    Topology.closure_interior_subset_closure (A := A)
  exact h_subset hx_cl

namespace Topology

variable {X : Type*} [TopologicalSpace X]

theorem AlphaOpen.frontier_eq_closure_diff_interior
    {A : Set X} (hA : AlphaOpen (A : Set X)) :
    frontier (A : Set X) = closure (A : Set X) \ interior (A : Set X) := by
  -- First, recall the characterisation of the frontier for an α-open set.
  have h₁ :
      frontier (A : Set X) =
        closure (interior (A : Set X)) \ interior (A : Set X) :=
    AlphaOpen.frontier_eq_closureInterior_diff_interior (A := A) hA
  -- For an α-open set, the two closures coincide.
  have h₂ :
      closure (A : Set X) = closure (interior (A : Set X)) :=
    AlphaOpen.closure_eq_closure_interior (A := A) hA
  -- Rewrite the previous equality using `h₂`.
  simpa [h₂] using h₁

end Topology

namespace Topology

theorem closure_closure_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (closure (interior (closure (A : Set X)))) =
      closure (interior (closure (A : Set X))) := by
  simpa [closure_closure]

end Topology

namespace Topology

/--
A set `A` is closed if and only if its closure is contained in `A`.
Equivalently, `closure A = A`.
-/
theorem isClosed_iff_closure_subset {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsClosed (A : Set X) ↔ closure (A : Set X) ⊆ A := by
  constructor
  · intro hAclosed
    -- If `A` is closed, its closure is itself.
    simpa [hAclosed.closure_eq] using (subset_rfl : (closure (A : Set X)) ⊆ closure A)
  · intro hSubset
    -- `closure A` is closed; if `closure A ⊆ A` then `A` equals its closure.
    have hEq : closure (A : Set X) = A :=
      Set.Subset.antisymm hSubset subset_closure
    simpa [hEq] using (isClosed_closure : IsClosed (closure (A : Set X)))

end Topology

namespace Topology

variable {X : Type*} [TopologicalSpace X]

theorem PreOpen.union_alpha {A B : Set X}
    (hA : PreOpen (A : Set X)) (hB : AlphaOpen (B : Set X)) :
    PreOpen (A ∪ B : Set X) := by
  -- Turn the α-open set `B` into a preopen set.
  have hBpre : PreOpen (B : Set X) := AlphaOpen.to_PreOpen hB
  -- Apply the union lemma for two preopen sets.
  simpa using PreOpen.union (A := A) (B := B) hA hBpre

end Topology

theorem Topology.AlphaOpen.union_frontier_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.AlphaOpen (A : Set X)) :
    (A : Set X) ∪ frontier (A : Set X) = closure (A : Set X) := by
  -- An α-open set is semi-open, so we may invoke the corresponding lemma.
  have hSemi : Topology.SemiOpen (A : Set X) :=
    Topology.AlphaOpen.to_SemiOpen hA
  simpa using
    Topology.SemiOpen.union_frontier_eq_closure (A := A) hSemi

theorem Topology.isClosed_iff_closure_subset'
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed (A : Set X) ↔ closure (A : Set X) ⊆ A := by
  constructor
  · intro hA
    -- If `A` is closed, its closure is `A` itself,
    -- so the required inclusion is immediate.
    simpa [hA.closure_eq] using
      (subset_rfl : closure (A : Set X) ⊆ closure (A : Set X))
  · intro hIncl
    -- Since `closure A ⊆ A` and the reverse inclusion
    -- `A ⊆ closure A` is always true, we have equality.
    have hEq : closure (A : Set X) = A :=
      Set.Subset.antisymm hIncl subset_closure
    -- A set equal to its closure is closed.
    simpa [hEq] using
      (isClosed_closure : IsClosed (closure (A : Set X)))

namespace Topology

theorem PreOpen_iff_subset_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    PreOpen (A : Set X) ↔ (A : Set X) ⊆ interior (closure (A : Set X)) := by
  -- `PreOpen` is defined exactly as the stated inclusion, so the equivalence
  -- follows by unfolding the definition.
  unfold PreOpen
  rfl

end Topology

theorem Topology.closure_union_interior_compl_univ
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (A : Set X) ∪ interior ((A : Set X)ᶜ) = (Set.univ : Set X) := by
  -- Rewrite `interior (Aᶜ)` as the complement of `closure A`.
  have h : interior ((A : Set X)ᶜ) = (closure (A : Set X))ᶜ :=
    interior_compl_eq_compl_closure (A := A)
  -- Substitute and simplify using `union_compl_self`.
  simpa [h, Set.union_compl_self]

theorem IsOpen.subset_interior {X : Type*} [TopologicalSpace X]
    {U S : Set X} (hU : IsOpen (U : Set X)) (hUS : (U : Set X) ⊆ S) :
    (U : Set X) ⊆ interior S := by
  intro x hxU
  -- `U` is an open neighbourhood of `x`.
  have hU_nhds : (U : Set X) ∈ 𝓝 x := hU.mem_nhds hxU
  -- Since `U ⊆ S`, the set `S` is also a neighbourhood of `x`.
  have hS_nhds : S ∈ 𝓝 x :=
    Filter.mem_of_superset hU_nhds hUS
  -- Translate the neighbourhood condition into membership
  -- of the interior of `S`.
  exact (mem_interior_iff_mem_nhds).2 hS_nhds

theorem interior_iUnion_interiors {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {A : ι → Set X} :
    interior (⋃ i, interior (A i) : Set X) = ⋃ i, interior (A i) := by
  -- Each `interior (A i)` is open.
  have hOpen : ∀ i, IsOpen (interior (A i) : Set X) := fun _ => isOpen_interior
  -- Apply the general lemma about interiors of unions of open sets.
  simpa using
    (Topology.interior_iUnion_of_open (A := fun i => interior (A i)) hOpen)

theorem interior_union_frontier_union_interior_compl_univ
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A : Set X) ∪ frontier (A : Set X) ∪ interior ((A : Set X)ᶜ) =
      (Set.univ : Set X) := by
  classical
  -- Step 1: rewrite `interior A ∪ frontier A` as `closure A`.
  have hIntFront :
      interior (A : Set X) ∪ frontier (A : Set X) =
        closure (A : Set X) := by
    have h := closure_eq_interior_union_frontier (A := A)
    simpa [Set.union_comm, Set.union_left_comm] using h.symm
  -- Step 2: rewrite `interior Aᶜ` as the complement of `closure A`.
  have hIntCompl :
      interior ((A : Set X)ᶜ) = (closure (A : Set X))ᶜ :=
    interior_compl_eq_compl_closure (A := A)
  -- Step 3: assemble the three parts.
  calc
    interior (A : Set X) ∪ frontier (A : Set X) ∪ interior ((A : Set X)ᶜ)
        = (interior (A : Set X) ∪ frontier (A : Set X)) ∪
          interior ((A : Set X)ᶜ) := by
          simp [Set.union_assoc]
    _ = closure (A : Set X) ∪ interior ((A : Set X)ᶜ) := by
          simpa [hIntFront]
    _ = closure (A : Set X) ∪ (closure (A : Set X))ᶜ := by
          simpa [hIntCompl]
    _ = (Set.univ : Set X) := by
          simpa using Set.union_compl_self (closure (A : Set X))

theorem isClosed_of_frontier_subset {X : Type*} [TopologicalSpace X] {A : Set X}
    (hFront : frontier (A : Set X) ⊆ A) : IsClosed (A : Set X) := by
  -- First, show `closure A ⊆ A`.
  have hIncl : closure (A : Set X) ⊆ A := by
    intro x hxCl
    -- Rewrite `hxCl : x ∈ closure A` using the decomposition of the closure.
    have hxUnion : x ∈ (A : Set X) ∪ frontier (A : Set X) := by
      simpa [closure_eq_self_union_frontier (A := A)] using hxCl
    -- Analyse the two cases and conclude membership in `A`.
    cases hxUnion with
    | inl hxA      => exact hxA
    | inr hxFr     => exact hFront hxFr
  -- Apply the characterisation `IsClosed A ↔ closure A ⊆ A`.
  exact (Topology.isClosed_iff_closure_subset (A := A)).2 hIncl

namespace Topology

variable {X : Type*} [TopologicalSpace X]

/--
For any family of sets `A i`, the union of the interiors of their closures
is contained in the interior of the closure of their union.
-/
theorem iUnion_interior_closure_subset_interior_closure_iUnion
    {ι : Sort*} {A : ι → Set X} :
    (⋃ i, interior (closure (A i))) ⊆ interior (closure (⋃ i, A i)) := by
  intro x hx
  -- Choose an index `i` with `x ∈ interior (closure (A i))`.
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- `A i` is contained in the union, hence so is its closure.
  have h_closure_subset :
      closure (A i) ⊆ closure (⋃ j, A j) := by
    apply closure_mono
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  -- Taking interiors preserves inclusions.
  have h_interior_subset :
      interior (closure (A i)) ⊆ interior (closure (⋃ j, A j)) :=
    interior_mono h_closure_subset
  -- Conclude the desired membership.
  exact h_interior_subset hx_i

end Topology

theorem closure_diff_frontier_eq_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (A : Set X) \ frontier (A : Set X) = interior (A : Set X) := by
  ext x
  constructor
  · intro hx
    -- `hx` gives membership in the closure and non-membership in the frontier.
    have hxCl : x ∈ closure (A : Set X) := hx.1
    have hxNotFr : x ∉ frontier (A : Set X) := hx.2
    -- Either `x` is in the interior of `A` or not.
    by_cases hxInt : x ∈ interior (A : Set X)
    · exact hxInt
    · -- If `x` is **not** in `interior A` but lies in `closure A`,
      -- then by definition it is in the frontier, contradicting `hxNotFr`.
      have : x ∈ frontier (A : Set X) := ⟨hxCl, hxInt⟩
      exact (hxNotFr this).elim
  · intro hxInt
    -- From `x ∈ interior A` we obtain `x ∈ closure A`.
    have hxCl : x ∈ closure (A : Set X) := subset_closure (interior_subset hxInt)
    -- Points of the interior never belong to the frontier.
    have hxNotFr : x ∉ frontier (A : Set X) := by
      intro hxFr
      -- `hxFr` gives `x ∉ interior A`, contradicting `hxInt`.
      exact (hxFr.2 hxInt)
    exact ⟨hxCl, hxNotFr⟩

namespace Topology

variable {X : Type*} [TopologicalSpace X]

theorem interior_interior_closure (A : Set X) :
    interior (interior (closure (A : Set X))) =
      interior (closure (A : Set X)) := by
  simpa [interior_interior]

end Topology

theorem Topology.PreOpen.of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure (A : Set X) = (Set.univ : Set X)) :
    PreOpen (A : Set X) := by
  unfold PreOpen
  intro x _hxA
  -- Since `closure A = univ`, its interior is also `univ`,
  -- hence every point belongs to it.
  simpa [hDense, interior_univ] using (Set.mem_univ x)

theorem isClosed_iff_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed (A : Set X) ↔ closure (A : Set X) = A := by
  constructor
  · intro hA
    simpa using hA.closure_eq
  · intro hEq
    have hClosed : IsClosed (closure (A : Set X)) := isClosed_closure
    simpa [hEq] using hClosed

theorem closure_iUnion_closure_eq {X : Type*} [TopologicalSpace X] {ι : Sort*}
    (A : ι → Set X) :
    closure (⋃ i, closure (A i) : Set X) = closure (⋃ i, A i) := by
  -- First inclusion: `⊆`.
  have h₁ : closure (⋃ i, closure (A i) : Set X) ⊆ closure (⋃ i, A i) := by
    -- `⋃ i, closure (A i)` is contained in `closure (⋃ i, A i)`.
    have hSub : (⋃ i, closure (A i) : Set X) ⊆ closure (⋃ i, A i) := by
      intro x hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
      -- `closure (A i)` is contained in the closure of the union.
      have : closure (A i : Set X) ⊆ closure (⋃ j, A j) :=
        closure_mono (Set.subset_iUnion _ _)
      exact this hx_i
    -- Apply the minimality of the closure.
    exact closure_minimal hSub isClosed_closure
  -- Second inclusion: `⊇`.
  have h₂ : closure (⋃ i, A i : Set X) ⊆ closure (⋃ i, closure (A i)) := by
    -- `⋃ i, A i` is contained in `⋃ i, closure (A i)`.
    have hSub : (⋃ i, A i : Set X) ⊆ ⋃ i, closure (A i) := by
      intro x hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
      exact Set.mem_iUnion.2 ⟨i, subset_closure hx_i⟩
    -- Taking closures preserves inclusions.
    exact closure_mono hSub
  -- Combine the two inclusions for the desired equality.
  exact Set.Subset.antisymm h₁ h₂

theorem interior_eq_empty_of_interior_closure_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (closure (A : Set X)) = (∅ : Set X)) :
    interior (A : Set X) = (∅ : Set X) := by
  -- We prove that `interior A` is contained in the empty set by contradiction.
  apply Set.eq_empty_iff_forall_not_mem.2
  intro x hxIntA
  -- From `hxIntA : x ∈ interior A` we derive
  -- `x ∈ interior (closure A)` using monotonicity of `interior`.
  have hxIntClA : x ∈ interior (closure (A : Set X)) := by
    -- `A ⊆ closure A`
    have hSub : (A : Set X) ⊆ closure (A : Set X) := subset_closure
    -- Hence `interior A ⊆ interior (closure A)`.
    exact (interior_mono hSub) hxIntA
  -- The assumption `h` says `interior (closure A)` is empty, contradicting `hxIntClA`.
  have : x ∈ (∅ : Set X) := by
    simpa [h] using hxIntClA
  exact this.elim



theorem frontier_inter_subset_frontier_and_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier (A ∩ B : Set X) ⊆
      (frontier (A : Set X) ∩ closure (B : Set X)) ∪
        (frontier (B : Set X) ∩ closure (A : Set X)) := by
  intro x hx
  -- Decompose the membership in the frontier of `A ∩ B`.
  have hxClAB : x ∈ closure (A ∩ B : Set X) := hx.1
  have hxNotIntAB : x ∉ interior (A ∩ B : Set X) := hx.2
  -- From the closure of the intersection we derive membership
  -- in each individual closure.
  have hxClA : x ∈ closure (A : Set X) :=
    (closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)) hxClAB
  have hxClB : x ∈ closure (B : Set X) :=
    (closure_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)) hxClAB
  -- Analyse the interior condition.
  by_cases hIntA : x ∈ interior (A : Set X)
  · by_cases hIntB : x ∈ interior (B : Set X)
    · -- If `x` is in both interiors then it is interior to `A ∩ B`,
      -- contradicting `hxNotIntAB`.
      have hOpen : IsOpen (interior (A : Set X) ∩ interior (B : Set X)) :=
        isOpen_interior.inter isOpen_interior
      have hxIn : x ∈ interior (A : Set X) ∩ interior (B : Set X) :=
        ⟨hIntA, hIntB⟩
      have hSubset :
          (interior (A : Set X) ∩ interior (B : Set X) : Set X) ⊆
            A ∩ B := by
        intro y hy
        exact ⟨interior_subset hy.1, interior_subset hy.2⟩
      have hxIntAB : x ∈ interior (A ∩ B : Set X) :=
        (mem_interior_iff_mem_nhds).2
          (Filter.mem_of_superset (hOpen.mem_nhds hxIn) hSubset)
      exact (hxNotIntAB hxIntAB).elim
    · -- `x ∉ interior B` ⇒ `x ∈ frontier B ∩ closure A`.
      have : x ∈ frontier (B : Set X) :=
        ⟨hxClB, hIntB⟩
      exact Or.inr ⟨this, hxClA⟩
  · -- `x ∉ interior A` ⇒ `x ∈ frontier A ∩ closure B`.
    have : x ∈ frontier (A : Set X) :=
      ⟨hxClA, hIntA⟩
    exact Or.inl ⟨this, hxClB⟩

namespace Topology

variable {X : Type*} [TopologicalSpace X]

/--
For a preopen set `A`, adjoining its frontier yields the whole closure.
-/
theorem PreOpen.union_frontier_eq_closure {A : Set X}
    (hA : PreOpen (A : Set X)) :
    (A : Set X) ∪ frontier (A : Set X) = closure (A : Set X) := by
  -- First, show the left‐hand side is contained in the closure.
  have h₁ : (A : Set X) ∪ frontier (A : Set X) ⊆ closure (A : Set X) := by
    intro x hx
    cases hx with
    | inl hxA      => exact subset_closure hxA
    | inr hxFront  => exact hxFront.1
  -- Conversely, take a point in `closure A` and place it in the union.
  have h₂ : closure (A : Set X) ⊆ (A : Set X) ∪ frontier (A : Set X) := by
    intro x hxCl
    by_cases hAx : x ∈ (A : Set X)
    · exact Or.inl hAx
    · -- Since `A` is preopen we have `A ⊆ interior (closure A)`.
      -- Hence `x ∉ A` implies `x ∉ interior A`, because
      -- `interior A ⊆ A`.
      have hNotIntA : x ∉ interior (A : Set X) := by
        intro hxInt
        exact (hAx : x ∉ A) (interior_subset hxInt)
      -- Combine `hxCl` and `hNotIntA` to see that `x` is on the frontier.
      exact Or.inr ⟨hxCl, hNotIntA⟩
  -- Establish the desired equality.
  exact Set.Subset.antisymm h₁ h₂

end Topology



theorem IsOpen.union_SemiOpen {X : Type*} [TopologicalSpace X] {U A : Set X}
    (hU : IsOpen (U : Set X)) (hA : Topology.SemiOpen (A : Set X)) :
    Topology.SemiOpen (U ∪ A : Set X) := by
  -- Reuse the existing lemma `Topology.SemiOpen.union_open`,
  -- switching the roles of the two sets via commutativity of `∪`.
  simpa [Set.union_comm] using
    (Topology.SemiOpen.union_open (A := A) (U := U) hA hU)

theorem Topology.SemiOpen.nonempty_iff_interior_closure_nonempty
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.SemiOpen (A : Set X)) :
    (A : Set X).Nonempty ↔ (interior (closure (A : Set X))).Nonempty := by
  classical
  constructor
  · intro hANon
    -- From semi-openness and non-emptiness of `A` we get
    -- non-emptiness of `interior A`.
    have hIntANon : (interior (A : Set X)).Nonempty :=
      Topology.SemiOpen.interior_nonempty_of_nonempty (A := A) hA hANon
    -- `interior A ⊆ interior (closure A)`.
    have hSubset :
        interior (A : Set X) ⊆ interior (closure (A : Set X)) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    rcases hIntANon with ⟨x, hxIntA⟩
    exact ⟨x, hSubset hxIntA⟩
  · intro hIntClNon
    rcases hIntClNon with ⟨x, hxIntCl⟩
    -- From `x ∈ interior (closure A)` we obtain `x ∈ closure A`.
    have hxCl : x ∈ closure (A : Set X) := interior_subset hxIntCl
    -- Using the neighbourhood characterisation of the closure with
    -- the open set `univ`, find a point of `A`.
    have hWitness :=
      (mem_closure_iff).1 hxCl (Set.univ) isOpen_univ (by simp)
    rcases hWitness with ⟨y, _hyUniv, hyA⟩
    exact ⟨y, hyA⟩

theorem Topology.AlphaOpen.union_closure_interior_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.AlphaOpen (A : Set X)) :
    (A : Set X) ∪ closure (interior (A : Set X)) = closure (A : Set X) := by
  -- First, prove the inclusion `⊆`.
  have h_subset_left : (A : Set X) ⊆ closure (A : Set X) := subset_closure
  have h_subset_right :
      closure (interior (A : Set X)) ⊆ closure (A : Set X) := by
    apply closure_mono
    exact interior_subset
  have h_union_subset :
      (A : Set X) ∪ closure (interior (A : Set X)) ⊆ closure (A : Set X) := by
    intro x hx
    cases hx with
    | inl hxA      => exact h_subset_left hxA
    | inr hxClInt  => exact h_subset_right hxClInt
  -- An α-open set is semi-open, hence the two closures coincide.
  have hSemi : Topology.SemiOpen (A : Set X) :=
    Topology.AlphaOpen.to_SemiOpen hA
  have h_cl_eq :
      closure (A : Set X) = closure (interior (A : Set X)) :=
    Topology.SemiOpen.closure_eq_closure_interior (A := A) hSemi
  -- Now, prove the inclusion `⊇`.
  have h_closure_subset_union :
      closure (A : Set X) ⊆ (A : Set X) ∪ closure (interior (A : Set X)) := by
    intro x hx
    have hx' : x ∈ closure (interior (A : Set X)) := by
      simpa [h_cl_eq] using hx
    exact Or.inr hx'
  -- Combine the two inclusions to obtain the desired equality.
  exact Set.Subset.antisymm h_union_subset h_closure_subset_union







theorem closure_iInter_interiors_subset_iInter_closures
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    closure (⋂ i, interior (A i) : Set X) ⊆ ⋂ i, closure (A i) := by
  intro x hx
  -- For each index `i`, we prove `x ∈ closure (A i)`.
  have hx_i : ∀ i, x ∈ closure (A i) := by
    intro i
    -- The intersection of the interiors is contained in `A i`.
    have h_subset : (⋂ j, interior (A j) : Set X) ⊆ A i := by
      intro y hy
      -- `hy` gives `y ∈ interior (A i)`; hence `y ∈ A i`.
      exact interior_subset ((Set.mem_iInter.1 hy) i)
    -- Taking closures preserves inclusions.
    have h_closure_subset :
        closure (⋂ j, interior (A j) : Set X) ⊆ closure (A i) :=
      closure_mono h_subset
    exact h_closure_subset hx
  -- Assemble the individual memberships into the intersection of closures.
  exact Set.mem_iInter.2 hx_i

theorem frontier_eq_empty_of_open_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_open  : IsOpen (A : Set X)) (hA_closed : IsClosed (A : Set X)) :
    frontier (A : Set X) = (∅ : Set X) := by
  -- Unfold the definition of the frontier.
  unfold frontier
  -- For a closed set, its closure is itself.
  have h_closure : closure (A : Set X) = A := hA_closed.closure_eq
  -- For an open set, its interior is itself.
  have h_interior : interior (A : Set X) = A := hA_open.interior_eq
  -- Rewrite using the two equalities and simplify.
  simpa [h_closure, h_interior, Set.diff_self]

theorem frontier_eq_closure_inter_closure_compl {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    frontier (A : Set X) = closure (A : Set X) ∩ closure (Aᶜ : Set X) := by
  classical
  -- `frontier A = closure A \ interior A`
  have h₁ : frontier (A : Set X) = closure (A : Set X) \ interior (A : Set X) := rfl
  -- `closure A \ interior A = closure A ∩ (interior A)ᶜ`
  have h₂ :
      closure (A : Set X) \ interior (A : Set X) =
        closure (A : Set X) ∩ (interior (A : Set X))ᶜ := by
    simp [Set.diff_eq, Set.inter_comm]
  -- `closure Aᶜ = (interior A)ᶜ`
  have h₃ :
      closure (Aᶜ : Set X) = (interior (A : Set X))ᶜ := by
    -- `closure_compl_eq_compl_interior` is in mathlib
    simpa using (closure_compl_eq_compl_interior (A := A)).symm
  -- Put everything together
  simpa [h₁, h₂, h₃, Set.inter_comm]

namespace Topology

theorem SemiOpen.eq_empty_of_interior_eq_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : SemiOpen (A : Set X))
    (hInt : interior (A : Set X) = (∅ : Set X)) :
    (A : Set X) = (∅ : Set X) := by
  ext x
  constructor
  · intro hxA
    -- From `SemiOpen` we know `x ∈ closure (interior A)`.
    have : x ∈ closure (interior (A : Set X)) := hA hxA
    -- But `interior A` is empty, hence so is its closure.
    simpa [hInt, closure_empty] using this
  · intro hx
    cases hx

end Topology

theorem closure_closure_left_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (closure (A : Set X) ∪ B) = closure (A ∪ B : Set X) := by
  -- First inclusion: `closure (closure A ∪ B) ⊆ closure (A ∪ B)`.
  have h₁ :
      closure (closure (A : Set X) ∪ B) ⊆ closure (A ∪ B : Set X) := by
    -- It suffices to show the subset relation for the sets *inside*
    -- the two closures and then use `closure_minimal`.
    have hSubset :
        (closure (A : Set X) ∪ B : Set X) ⊆ closure (A ∪ B : Set X) := by
      intro x hx
      cases hx with
      | inl hxClA =>
          -- `closure A ⊆ closure (A ∪ B)`
          have hIncl :
              closure (A : Set X) ⊆ closure (A ∪ B : Set X) :=
            closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
          exact hIncl hxClA
      | inr hxB =>
          -- `x ∈ B ⊆ closure B`, then argue as above.
          have hxClB : x ∈ closure (B : Set X) := subset_closure hxB
          have hIncl :
              closure (B : Set X) ⊆ closure (A ∪ B : Set X) :=
            closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
          exact hIncl hxClB
    exact closure_minimal hSubset isClosed_closure
  -- Second inclusion: `closure (A ∪ B) ⊆ closure (closure A ∪ B)`.
  have h₂ :
      closure (A ∪ B : Set X) ⊆ closure (closure (A : Set X) ∪ B) := by
    -- Show the inclusion for the sets inside the closures.
    have hSubset :
        (A ∪ B : Set X) ⊆ closure (A : Set X) ∪ B := by
      intro x hx
      cases hx with
      | inl hxA =>
          exact Or.inl (subset_closure hxA)
      | inr hxB =>
          exact Or.inr hxB
    exact closure_mono hSubset
  -- Combine the two inclusions.
  exact Set.Subset.antisymm h₁ h₂

theorem IsClosed.interior_union_frontier_eq {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed (A : Set X)) :
    interior (A : Set X) ∪ frontier (A : Set X) = A := by
  -- Express the frontier of a closed set as a set difference.
  have hFront :
      frontier (A : Set X) = A \ interior (A : Set X) :=
    IsClosed.frontier_eq_diff_interior (A := A) hA
  -- Prove the desired equality by showing mutual inclusions.
  ext x
  constructor
  · intro hx
    cases hx with
    | inl hxInt =>
        -- `x` lies in `interior A`, hence in `A`.
        exact interior_subset hxInt
    | inr hxFront =>
        -- Rewrite `hxFront` using `hFront` and extract membership in `A`.
        have : x ∈ A \ interior (A : Set X) := by
          simpa [hFront] using hxFront
        exact this.1
  · intro hxA
    -- Split on whether `x` is interior to `A`.
    by_cases hxInt : x ∈ interior (A : Set X)
    · exact Or.inl hxInt
    · -- Otherwise `x` is in the frontier via `hFront`.
      have : x ∈ A \ interior (A : Set X) := ⟨hxA, hxInt⟩
      have hxFront : x ∈ frontier (A : Set X) := by
        simpa [hFront] using this
      exact Or.inr hxFront

theorem Topology.SemiOpen.frontier_eq_frontier_inter_closureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.SemiOpen (A : Set X)) :
    frontier (A : Set X) =
      frontier (A : Set X) ∩ closure (interior (A : Set X)) := by
  -- We establish the two inclusions separately and use `Set.Subset.antisymm`.
  apply Set.Subset.antisymm
  · -- A point in the frontier lies in the required intersection
    intro x hxFr
    -- For a semi-open set, the frontier is contained in `closure (interior A)`.
    have hxClInt :
        x ∈ closure (interior (A : Set X)) :=
      Topology.SemiOpen.frontier_subset_closure_interior
        (A := A) hA hxFr
    exact And.intro hxFr hxClInt
  · -- The intersection is contained in the frontier by projection
    intro x hx
    exact hx.1

theorem frontier_interior_closure_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (interior (closure (A : Set X))) ⊆ closure (A : Set X) := by
  intro x hx
  -- First, move from the frontier of `interior (closure A)` to the frontier of `A`.
  have hFront : x ∈ frontier (A : Set X) :=
    (frontier_interior_closure_subset_frontier (A := A)) hx
  -- The frontier of any set is contained in its closure.
  exact (Topology.frontier_subset_closure (A := A)) hFront

theorem IsClosed.closure_interior_subset {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed (A : Set X)) :
    closure (interior (A : Set X)) ⊆ A := by
  -- `interior A ⊆ A` by definition of `interior`.
  have hSubset : (interior (A : Set X) : Set X) ⊆ A := interior_subset
  -- Taking closures preserves inclusions.
  have hClosureSubset : closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
    closure_mono hSubset
  -- Since `A` is closed, its closure is itself.
  simpa [hA.closure_eq] using hClosureSubset

theorem closure_diff_closureInterior_subset_frontier {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) \ closure (interior (A : Set X)) ⊆
      frontier (A : Set X) := by
  intro x hx
  -- Decompose the hypothesis into its two components.
  have hxCl : x ∈ closure (A : Set X) := hx.1
  have hxNotClInt : x ∉ closure (interior (A : Set X)) := hx.2
  -- Show that `x` is not in the interior of `A`.
  have hxNotInt : x ∉ interior (A : Set X) := by
    intro hxInt
    have : x ∈ closure (interior (A : Set X)) := subset_closure hxInt
    exact hxNotClInt this
  -- Combine the facts to obtain membership in the frontier.
  exact ⟨hxCl, hxNotInt⟩

theorem frontier_inter_closure_eq_frontier {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    frontier (A : Set X) ∩ closure (A : Set X) = frontier (A : Set X) := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    have hxCl : x ∈ closure (A : Set X) := hx.1
    exact ⟨hx, hxCl⟩

namespace Topology

theorem PreOpen.frontier_closure_eq_frontier_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : PreOpen (A : Set X)) :
    frontier (closure (A : Set X)) =
      frontier (interior (closure (A : Set X))) := by
  -- The closure of a preopen set is semi-open.
  have hSemi : SemiOpen (closure (A : Set X)) :=
    PreOpen.closure_SemiOpen hA
  -- Apply the frontier lemma for semi-open sets to `closure A`.
  simpa using
    SemiOpen.frontier_eq_frontier_interior
      (A := closure (A : Set X)) hSemi

end Topology



theorem interior_closure_univ {X : Type*} [TopologicalSpace X] :
    interior (closure (Set.univ : Set X)) = (Set.univ : Set X) := by
  simpa [closure_univ, interior_univ]

namespace Topology

variable {X : Type*} [TopologicalSpace X]

theorem closure_subset_of_subset_interior {A B : Set X}
    (h : (A : Set X) ⊆ interior (B : Set X)) :
    closure (A : Set X) ⊆ closure (B : Set X) := by
  -- From `h` and `interior_subset` we obtain `A ⊆ B`.
  have hAB : (A : Set X) ⊆ B := by
    intro x hxA
    exact interior_subset (h hxA)
  -- Taking closures preserves inclusions.
  exact closure_mono hAB

end Topology

namespace Topology

theorem closure_subset_of_subset_interior'
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : (B : Set X) ⊆ interior (closure (A : Set X))) :
    closure (B : Set X) ⊆ closure (A : Set X) := by
  simpa using
    closure_subset_of_subset_interior_closure (A := A) (B := B) h

end Topology

theorem IsClosed.frontier_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    frontier (closure (A : Set X)) = frontier (A : Set X) := by
  -- Unfold the definition of `frontier` and use properties of closed sets.
  have h₁ : closure (A : Set X) = A := hA.closure_eq
  have h₂ : interior (closure (A : Set X)) = interior (A : Set X) := by
    simpa [h₁] using IsClosed.interior_closure_eq (A := A) hA
  simp [frontier, closure_closure, h₁, h₂]

theorem interior_closure_subset_self_union_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) ⊆ (A : Set X) ∪ frontier (A : Set X) := by
  intro x hxInt
  by_cases hxA : x ∈ (A : Set X)
  · exact Or.inl hxA
  ·
    -- `x` lies in the closure of `A` because it is in the interior of that closure.
    have hxCl : x ∈ closure (A : Set X) := interior_subset hxInt
    -- Since `x ∉ A` and `interior A ⊆ A`, we also have `x ∉ interior A`.
    have hxNotIntA : x ∉ interior (A : Set X) := by
      intro hxIntA
      exact hxA (interior_subset hxIntA)
    -- Hence `x` lies in the frontier of `A`.
    exact Or.inr ⟨hxCl, hxNotIntA⟩

theorem frontier_eq_empty_iff_open_closed
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (A : Set X) = (∅ : Set X) ↔
      IsOpen (A : Set X) ∧ IsClosed (A : Set X) := by
  classical
  constructor
  · intro hFront
    -- `frontier A = ∅` implies `closure A ⊆ interior A`
    have hClSubInt : closure (A : Set X) ⊆ interior (A : Set X) := by
      intro x hxCl
      by_cases hxInt : x ∈ interior (A : Set X)
      · exact hxInt
      ·
        have hxFront : x ∈ frontier (A : Set X) := ⟨hxCl, hxInt⟩
        have : x ∈ (∅ : Set X) := by
          simpa [hFront] using hxFront
        exact this.elim
    -- Hence `A ⊆ interior A`
    have hASubInt : (A : Set X) ⊆ interior (A : Set X) := by
      intro x hxA
      exact hClSubInt (subset_closure hxA)
    -- And always `interior A ⊆ A`
    have hIntSubA : interior (A : Set X) ⊆ A := interior_subset
    -- Thus `A = interior A`
    have hIntEq : interior (A : Set X) = A :=
      Set.Subset.antisymm hIntSubA hASubInt
    -- So `A` is open
    have hOpen : IsOpen (A : Set X) := by
      simpa [hIntEq] using (isOpen_interior : IsOpen (interior (A : Set X)))
    -- Moreover, `closure A ⊆ A`
    have hClSubA : closure (A : Set X) ⊆ A :=
      (hClSubInt.trans hIntSubA)
    -- Always `A ⊆ closure A`
    have hACl : (A : Set X) ⊆ closure (A : Set X) := subset_closure
    -- Hence `closure A = A`, so `A` is closed
    have hClosed : IsClosed (A : Set X) := by
      have hEq : closure (A : Set X) = A :=
        Set.Subset.antisymm hClSubA hACl
      simpa [hEq] using
        (isClosed_closure : IsClosed (closure (A : Set X)))
    exact And.intro hOpen hClosed
  · rintro ⟨hOpen, hClosed⟩
    exact frontier_eq_empty_of_open_closed (A := A) hOpen hClosed

theorem closureInterior_diff_interior_subset_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (A : Set X)) \ interior (A : Set X) ⊆
      frontier (A : Set X) := by
  intro x hx
  -- Decompose the membership in the set difference.
  have hxClInt : x ∈ closure (interior (A : Set X)) := hx.1
  have hxNotInt : x ∉ interior (A : Set X) := hx.2
  -- Since `interior A ⊆ A`, we have `closure (interior A) ⊆ closure A`.
  have hSubset :
      closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
    closure_mono (interior_subset : interior (A : Set X) ⊆ A)
  -- Hence `x ∈ closure A`.
  have hxClA : x ∈ closure (A : Set X) := hSubset hxClInt
  -- Combine the two facts to obtain membership in the frontier.
  exact ⟨hxClA, hxNotInt⟩

theorem frontier_univ {X : Type*} [TopologicalSpace X] :
    frontier (Set.univ : Set X) = (∅ : Set X) := by
  -- By definition, `frontier A = closure A \ interior A`.
  unfold frontier
  -- For the whole space, both the closure and the interior are `univ`.
  simp [closure_univ, interior_univ, Set.diff_self]

theorem interior_union_closures_subset_interior_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A : Set X) ∪ closure (B : Set X)) ⊆
      interior (closure (A ∪ B : Set X)) := by
  -- First, recall the inclusion `closure A ∪ closure B ⊆ closure (A ∪ B)`.
  have hsubset :
      (closure (A : Set X) ∪ closure (B : Set X) : Set X) ⊆
        closure (A ∪ B : Set X) :=
    closure_union_subset
  -- Monotonicity of `interior` yields the desired inclusion.
  exact interior_mono hsubset

theorem Topology.AlphaOpen.frontier_eq_empty_of_closed {X : Type*}
    [TopologicalSpace X] {A : Set X} (hClosed : IsClosed (A : Set X))
    (hAlpha : Topology.AlphaOpen (A : Set X)) :
    frontier (A : Set X) = (∅ : Set X) := by
  -- For a closed α-open set, we have `interior A = A`.
  have hInt : interior (A : Set X) = A :=
    Topology.AlphaOpen.closed_interior_eq (A := A) hClosed hAlpha
  -- And, because `A` is closed, `closure A = A`.
  have hCl : closure (A : Set X) = A := hClosed.closure_eq
  -- Substitute these equalities into the definition of `frontier`.
  unfold frontier
  simpa [hCl, hInt, Set.diff_self]

theorem Topology.SemiOpen.frontier_subset_of_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : Topology.SemiOpen (A : Set X)) (hBA : (B : Set X) ⊆ A) :
    frontier (B : Set X) ⊆ closure (interior (A : Set X)) := by
  intro x hxFrontB
  -- From `hBA`, the frontier of `B` is contained in `closure A`.
  have hxClA : x ∈ closure (A : Set X) :=
    (Topology.frontier_subset_closure_of_subset (A := B) (B := A) hBA) hxFrontB
  -- A semi-open set satisfies `closure A ⊆ closure (interior A)`.
  have hIncl : closure (A : Set X) ⊆ closure (interior (A : Set X)) :=
    Topology.SemiOpen.closure_subset hA
  exact hIncl hxClA

theorem IsOpen.frontier_subset_compl {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    frontier (A : Set X) ⊆ (A : Set X)ᶜ := by
  intro x hx
  -- `hx` gives `x ∉ interior A`
  have hxNotInt : x ∉ interior (A : Set X) := hx.2
  -- For an open set, `interior A = A`.
  have hInt : interior (A : Set X) = A := hA.interior_eq
  -- Hence `x ∉ A`.
  have hxNotA : x ∉ (A : Set X) := by
    simpa [hInt] using hxNotInt
  -- Conclude `x ∈ Aᶜ`.
  exact hxNotA

theorem Continuous.image_closure_subset_closure_image
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : Continuous f) {S : Set X} :
    f '' closure (S : Set X) ⊆ closure (f '' S) := by
  rintro y ⟨x, hxCl, rfl⟩
  -- We show `f x` is in the closure of `f '' S` using the neighbourhood
  -- characterisation of the closure.
  refine (mem_closure_iff).2 ?_
  intro V hVopen hxV
  -- The preimage of the open set `V` is an open neighbourhood of `x`.
  have hPreOpen : IsOpen (f ⁻¹' V) := hVopen.preimage hf
  have hxPre    : x ∈ f ⁻¹' V := hxV
  -- Because `x ∈ closure S`, this neighbourhood meets `S`.
  have hNonempty : ((f ⁻¹' V) ∩ S).Nonempty :=
    (mem_closure_iff).1 hxCl (f ⁻¹' V) hPreOpen hxPre
  rcases hNonempty with ⟨z, ⟨hzPre, hzS⟩⟩
  -- Map the witness back into `V ∩ f '' S`.
  exact ⟨f z, ⟨hzPre, ⟨z, hzS, rfl⟩⟩⟩

theorem IsOpen.closure_frontier_eq_closure_diff {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen (A : Set X)) :
    closure (frontier (A : Set X)) = closure (A : Set X) \ A := by
  -- `frontier A` is closed, hence its closure is itself.
  have h₁ : closure (frontier (A : Set X)) = frontier (A : Set X) :=
    closure_frontier_eq (A := A)
  -- For an open set, `frontier A = closure A \ A`.
  have h₂ : frontier (A : Set X) = closure (A : Set X) \ A :=
    IsOpen.frontier_eq_closure_diff (A := A) hA
  -- Combine the two equalities.
  simpa [h₂] using h₁

theorem closure_union_frontier_eq_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure ((A : Set X) ∪ frontier (A : Set X)) = closure (A : Set X) := by
  -- First inclusion: the closure of the union is contained in `closure A`,
  -- because both `A` and `frontier A` are.
  have h₁ :
      closure ((A : Set X) ∪ frontier (A : Set X)) ⊆ closure (A : Set X) := by
    -- The union itself is contained in `closure A`.
    have hSub : (A : Set X) ∪ frontier (A : Set X) ⊆ closure (A : Set X) := by
      intro x hx
      cases hx with
      | inl hxA      => exact subset_closure hxA
      | inr hxFront  => exact hxFront.1
    -- Use the minimality of the closure with respect to closed supersets.
    exact closure_minimal hSub isClosed_closure
  -- Second inclusion: `closure A` is contained in the closure of the union,
  -- since `A ⊆ A ∪ frontier A`.
  have h₂ :
      closure (A : Set X) ⊆ closure ((A : Set X) ∪ frontier (A : Set X)) :=
    closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ frontier A)
  -- Combine the two inclusions to obtain the desired equality.
  exact Set.Subset.antisymm h₁ h₂

theorem closure_union_closures_eq {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (closure (A : Set X) ∪ closure (B : Set X)) =
      closure (A : Set X) ∪ closure (B : Set X) := by
  -- The union of two closed sets is closed.
  have hClosed : IsClosed (closure (A : Set X) ∪ closure (B : Set X)) :=
    (isClosed_closure : IsClosed (closure (A : Set X))).union
      (isClosed_closure : IsClosed (closure (B : Set X)))
  -- The closure of a closed set is itself.
  simpa using hClosed.closure_eq

theorem frontier_empty {X : Type*} [TopologicalSpace X] :
    frontier (∅ : Set X) = (∅ : Set X) := by
  -- By definition, `frontier A = closure A \ interior A`.
  unfold frontier
  simp

theorem closure_inter_diff_union_eq_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A ∩ B : Set X) ∪ closure (A \ B : Set X) = closure (A : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    cases hx with
    | inl hxInter =>
        -- `A ∩ B ⊆ A`
        have hSub : closure (A ∩ B : Set X) ⊆ closure (A : Set X) :=
          closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)
        exact hSub hxInter
    | inr hxDiff =>
        -- `A \ B ⊆ A`
        have hSub : closure (A \ B : Set X) ⊆ closure (A : Set X) :=
          closure_mono (Set.diff_subset : (A \ B : Set X) ⊆ A)
        exact hSub hxDiff
  · intro x hxClA
    -- Decompose `A` into the disjoint union of `A ∩ B` and `A \ B`.
    have hDecomp :
        (A : Set X) ⊆ (A ∩ B : Set X) ∪ (A \ B : Set X) := by
      intro y hy
      by_cases hB : y ∈ B
      · exact Or.inl ⟨hy, hB⟩
      · exact Or.inr ⟨hy, hB⟩
    -- Monotonicity of `closure` applied to the above inclusion.
    have hStep₁ :
        closure (A : Set X) ⊆
          closure ((A ∩ B : Set X) ∪ (A \ B : Set X)) :=
      closure_mono hDecomp
    -- `closure (S ∪ T) ⊆ closure S ∪ closure T`.
    have hStep₂ :
        closure ((A ∩ B : Set X) ∪ (A \ B : Set X)) ⊆
          closure (A ∩ B : Set X) ∪ closure (A \ B : Set X) :=
      closure_union_subset_union_closure
    -- Chain the two inclusions to conclude.
    have : x ∈ closure (A ∩ B : Set X) ∪ closure (A \ B : Set X) :=
      hStep₂ (hStep₁ hxClA)
    exact this

theorem IsOpen.inter_SemiOpen {X : Type*} [TopologicalSpace X] {U A : Set X}
    (hU : IsOpen (U : Set X)) (hA : Topology.SemiOpen (A : Set X)) :
    Topology.SemiOpen (U ∩ A : Set X) := by
  simpa [Set.inter_comm] using
    Topology.SemiOpen.inter_open (A := A) (U := U) hA hU

theorem closure_iInter_of_closed {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {A : ι → Set X} (hA : ∀ i, IsClosed (A i)) :
    closure (⋂ i, A i : Set X) = ⋂ i, A i := by
  -- The intersection of closed sets is itself closed.
  have hClosed : IsClosed (⋂ i, A i : Set X) := isClosed_iInter hA
  -- Taking the closure of a closed set leaves it unchanged.
  simpa using hClosed.closure_eq

theorem interior_subset_closure_of_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : (A : Set X) ⊆ B) :
    interior (A : Set X) ⊆ closure (B : Set X) := by
  intro x hxIntA
  -- From `hxIntA` we have `x ∈ A`.
  have hxA : x ∈ (A : Set X) := interior_subset hxIntA
  -- Using the inclusion `A ⊆ B`, we obtain `x ∈ B`.
  have hxB : x ∈ (B : Set X) := hAB hxA
  -- Every point of `B` lies in `closure B`.
  exact subset_closure hxB

theorem IsOpen.frontier_eq_frontier_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen (A : Set X)) :
    frontier (A : Set X) = frontier (interior (A : Set X)) := by
  simpa [hA.interior_eq]







theorem interior_inter_interior_compl_eq_empty {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (A : Set X) ∩ interior ((A : Set X)ᶜ) = (∅ : Set X) := by
  ext x
  constructor
  · intro hx
    have hA  : x ∈ (A : Set X) := interior_subset hx.1
    have hAc : x ∈ ((A : Set X)ᶜ) := interior_subset hx.2
    exact (hAc hA).elim
  · intro hx
    cases hx

theorem frontier_inter_self {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (A : Set X) ∩ A = A \ interior (A : Set X) := by
  -- Unfold `frontier`.
  unfold frontier
  -- Work elementwise.
  ext x
  constructor
  · intro hx
    -- `hx` encodes that
    --   • `x ∈ closure A`            (`hx.1.1`)
    --   • `x ∉ interior A`           (`hx.1.2`)
    --   • `x ∈ A`                    (`hx.2`)
    -- so `x` satisfies the right-hand side.
    exact ⟨hx.2, hx.1.2⟩
  · intro hx
    -- `hx` says `x ∈ A` and `x ∉ interior A`.
    -- The first item gives `x ∈ closure A`.
    have hxCl : x ∈ closure (A : Set X) := subset_closure hx.1
    -- Assemble the data required for the left side.
    exact ⟨⟨hxCl, hx.2⟩, hx.1⟩

theorem frontier_subset_compl_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    frontier (A : Set X) ⊆ (interior (A : Set X))ᶜ := by
  intro x hx
  exact hx.2

theorem interior_inter_left_isOpen {X : Type*} [TopologicalSpace X]
    {U A : Set X} (hU : IsOpen (U : Set X)) :
    interior (U ∩ A : Set X) = U ∩ interior (A : Set X) := by
  -- First, apply the general lemma about the interior of an intersection.
  have h₁ :
      interior (U ∩ A : Set X) =
        interior (U : Set X) ∩ interior (A : Set X) := by
    simpa using interior_inter (U : Set X) (A : Set X)
  -- Since `U` is open, its interior is itself.
  simpa [hU.interior_eq] using h₁

theorem Topology.SemiOpen.closure_interior_closure_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.SemiOpen (A : Set X)) :
    closure (interior (closure (A : Set X))) = closure (A : Set X) := by
  -- First, relate `closure (interior (closure A))` to `closure (interior A)`.
  have h₁ :=
    Topology.SemiOpen.closure_interior_closure_eq_closure_interior
      (A := A) hA
  -- Next, relate `closure (interior A)` to `closure A`.
  have h₂ :=
    (Topology.SemiOpen.closure_eq_closure_interior (A := A) hA).symm
  -- Combine the two equalities.
  exact h₁.trans h₂

theorem IsOpen.closure_eq_set_union_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    closure (A : Set X) = A ∪ frontier (A : Set X) := by
  simpa [hA.interior_eq] using
    (closure_eq_interior_union_frontier (A := A))

namespace Topology

variable {X : Type*} [TopologicalSpace X]

theorem SemiOpen.closure_frontier_subset_closure_interior
    {A : Set X} (hA : SemiOpen (A : Set X)) :
    closure (frontier (A : Set X)) ⊆ closure (interior (A : Set X)) := by
  -- The frontier is already contained in `closure (interior A)`.
  have hsubset :
      frontier (A : Set X) ⊆ closure (interior (A : Set X)) :=
    SemiOpen.frontier_subset_closure_interior (A := A) hA
  -- Taking closures preserves inclusions.
  simpa [closure_closure] using closure_mono hsubset

end Topology