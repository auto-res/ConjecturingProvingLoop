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


theorem P3_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P3 A := by
  intro h
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := h hx
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono (closure_mono interior_subset)
  exact hsubset hx'

theorem P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A := by
  intro x hx
  have hx_intA : x ∈ interior A := by
    simpa [hA.interior_eq] using hx
  have hsubset : interior A ⊆ interior (closure A) :=
    interior_mono subset_closure
  have hx_int_closA : x ∈ interior (closure A) := hsubset hx_intA
  simpa [hA.interior_eq] using hx_int_closA

theorem P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P3 A := by
  exact P3_of_P2 (P2_of_open hA)

theorem P1_and_P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ∧ P2 A → P3 A := by
  rintro ⟨_, hP2⟩
  exact P3_of_P2 hP2

theorem P1_and_P3_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ∧ P3 A → P2 A := by
  rintro ⟨hP1, hP3⟩
  intro x hx
  -- `x ∈ interior (closure A)` by `P3`
  have hx_int_closureA : x ∈ interior (closure A) := hP3 hx
  -- `closure A ⊆ closure (interior A)` thanks to `P1`
  have h_closure_subset : closure A ⊆ closure (interior A) := by
    simpa [closure_closure] using (closure_mono hP1)
  -- taking interiors preserves the inclusion
  have h_subset :
      interior (closure A) ⊆ interior (closure (interior A)) :=
    interior_mono h_closure_subset
  exact h_subset hx_int_closureA

theorem exists_open_neighborhood_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P3 A) : ∀ x ∈ A, ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ closure A := by
  intro x hx
  have hx_int : x ∈ interior (closure A) := hA hx
  refine ⟨interior (closure A), isOpen_interior, hx_int, ?_⟩
  exact interior_subset

theorem eq_empty_of_P1_and_interior_empty {X : Type*} [TopologicalSpace X] {A : Set X} (h1 : P1 A) (h2 : interior A = ∅) : A = ∅ := by
  ext x
  constructor
  · intro hxA
    have hx_closure : x ∈ closure (interior A) := h1 hxA
    simpa [h2, closure_empty] using hx_closure
  · intro hxEmpty
    cases hxEmpty

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : closure A = Set.univ) : P3 A := by
  intro x hx
  simpa [hA, interior_univ] using (Set.mem_univ x)

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P1 A) (hB : P1 B) : P1 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x` comes from `A`
      have hx_closure : x ∈ closure (interior A) := hA hxA
      -- `interior A ⊆ interior (A ∪ B)`
      have hsubset_int : interior A ⊆ interior (A ∪ B) := by
        apply interior_mono
        intro y hy
        exact Or.inl hy
      -- take closures of the previous inclusion
      have hsubset : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hsubset_int
      exact hsubset hx_closure
  | inr hxB =>
      -- `x` comes from `B`
      have hx_closure : x ∈ closure (interior B) := hB hxB
      -- `interior B ⊆ interior (A ∪ B)`
      have hsubset_int : interior B ⊆ interior (A ∪ B) := by
        apply interior_mono
        intro y hy
        exact Or.inr hy
      -- take closures of the previous inclusion
      have hsubset : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hsubset_int
      exact hsubset hx_closure

theorem exists_open_neighborhood_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : ∀ x ∈ A, ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ closure (interior A) := by
  intro x hx
  have hx_int : x ∈ interior (closure (interior A)) := hA hx
  refine ⟨interior (closure (interior A)), isOpen_interior, hx_int, ?_⟩
  exact interior_subset

theorem P1_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P1 A := by
  intro hP2 x hx
  exact interior_subset (hP2 hx)

theorem P1_and_not_P3_implies_not_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ∧ ¬ P3 A → ¬ P2 A := by
  rintro ⟨hP1, hnotP3⟩ hP2
  have hP3 : P3 A := P1_and_P2_implies_P3 ⟨hP1, hP2⟩
  exact hnotP3 hP3

theorem open_iff_P1_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : (P1 A ↔ P2 A) := by
  constructor
  · intro _; exact P2_of_open hA
  · exact P1_of_P2

theorem P1_iff_closure_interior_eq_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ closure (interior A) = closure A := by
  constructor
  · intro hP1
    apply subset_antisymm
    · -- `closure (interior A) ⊆ closure A`
      exact closure_mono interior_subset
    · -- `closure A ⊆ closure (interior A)` comes from `P1`
      have h : closure A ⊆ closure (closure (interior A)) := closure_mono hP1
      simpa [closure_closure] using h
  · intro hEq
    intro x hx
    -- since `x ∈ A ⊆ closure A = closure (interior A)`
    have : x ∈ closure A := subset_closure hx
    simpa [hEq] using this

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P2 A) (hB : P2 B) : P2 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x` comes from `A`
      have hx_int : x ∈ interior (closure (interior A)) := hA hxA
      -- build the required inclusion
      have hsubset :
          interior (closure (interior A)) ⊆
            interior (closure (interior (A ∪ B))) := by
        -- `A ⊆ A ∪ B`
        have h0 : (A : Set X) ⊆ A ∪ B := by
          intro z hz
          exact Or.inl hz
        -- apply monotonicity of the operators
        have h1 : interior A ⊆ interior (A ∪ B) := interior_mono h0
        have h2 : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
          closure_mono h1
        exact interior_mono h2
      exact hsubset hx_int
  | inr hxB =>
      -- `x` comes from `B`
      have hx_int : x ∈ interior (closure (interior B)) := hB hxB
      have hsubset :
          interior (closure (interior B)) ⊆
            interior (closure (interior (A ∪ B))) := by
        -- `B ⊆ A ∪ B`
        have h0 : (B : Set X) ⊆ A ∪ B := by
          intro z hz
          exact Or.inr hz
        have h1 : interior B ⊆ interior (A ∪ B) := interior_mono h0
        have h2 : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
          closure_mono h1
        exact interior_mono h2
      exact hsubset hx_int

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hA : closure (interior A) = Set.univ) : Topology.P2 A := by
  intro x hx
  simpa [hA, interior_univ] using (Set.mem_univ x)

theorem P1_Union {X : Type*} [TopologicalSpace X] {ι : Type*} {F : ι → Set X} (hF : ∀ i, Topology.P1 (F i)) : Topology.P1 (⋃ i, F i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxFi⟩
  have hxi : x ∈ closure (interior (F i)) := (hF i) hxFi
  have hsubset : closure (interior (F i)) ⊆ closure (interior (⋃ j, F j)) := by
    have h_subset_F : (F i : Set X) ⊆ ⋃ j, F j := by
      intro y hy
      exact Set.mem_iUnion_of_mem i hy
    have hsubset_int : interior (F i) ⊆ interior (⋃ j, F j) :=
      interior_mono h_subset_F
    exact closure_mono hsubset_int
  exact hsubset hxi

theorem P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = Set.univ) : Topology.P3 A := by
  exact P3_of_P2 (P2_of_dense_interior h)

theorem P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = Set.univ) : Topology.P1 A := P1_of_P2 (P2_of_dense_interior h)

theorem P1_and_P2_implies_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A → Topology.P2 A → closure (interior A) = closure A := by
  intro hP1 hP2
  exact (P1_iff_closure_interior_eq_closure).1 hP1

theorem P2_Union {X : Type*} [TopologicalSpace X] {ι : Type*} {F : ι → Set X} : (∀ i, Topology.P2 (F i)) → Topology.P2 (⋃ i, F i) := by
  intro hF
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxFi⟩
  have hxi : x ∈ interior (closure (interior (F i))) := (hF i) hxFi
  have hsubset :
      interior (closure (interior (F i)))
        ⊆ interior (closure (interior (⋃ j, F j))) := by
    -- `F i ⊆ ⋃ j, F j`
    have h₁ : (F i : Set X) ⊆ ⋃ j, F j := by
      intro y hy
      exact Set.mem_iUnion_of_mem i hy
    -- take interiors, closures, and interiors again
    have h₂ : interior (F i) ⊆ interior (⋃ j, F j) := interior_mono h₁
    have h₃ :
        closure (interior (F i)) ⊆ closure (interior (⋃ j, F j)) :=
      closure_mono h₂
    exact interior_mono h₃
  exact hsubset hxi

theorem P3_Union {X : Type*} [TopologicalSpace X] {ι : Type*} {F : ι → Set X} : (∀ i, Topology.P3 (F i)) → Topology.P3 (⋃ i, F i) := by
  intro hF x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxFi⟩
  have hxi : x ∈ interior (closure (F i)) := (hF i) hxFi
  have hsubset : interior (closure (F i)) ⊆ interior (closure (⋃ j, F j)) := by
    -- `F i ⊆ ⋃ j, F j`
    have h₁ : (F i : Set X) ⊆ ⋃ j, F j := by
      intro y hy
      exact Set.mem_iUnion_of_mem i hy
    -- apply monotonicity of closure and interior
    have h₂ : closure (F i) ⊆ closure (⋃ j, F j) := closure_mono h₁
    exact interior_mono h₂
  exact hsubset hxi

theorem open_of_closed_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → Topology.P3 A → IsOpen A := by
  intro hClosed hP3
  -- First, show `A ⊆ interior A`.
  have hsubset : (A : Set X) ⊆ interior A := by
    intro x hx
    have hx' : x ∈ interior (closure A) := hP3 hx
    simpa [hClosed.closure_eq] using hx'
  -- Hence `interior A = A`.
  have hEq : interior A = A := by
    apply Set.Subset.antisymm
    · exact interior_subset
    · exact hsubset
  -- Since `interior A` is open, so is `A`.
  have : IsOpen (interior A) := isOpen_interior
  simpa [hEq] using this

theorem P1_and_P3_equiv_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : (Topology.P1 A ∧ Topology.P3 A) ↔ Topology.P2 A := by
  constructor
  · exact P1_and_P3_implies_P2
  · intro hP2
    exact ⟨P1_of_P2 hP2, P3_of_P2 hP2⟩

theorem exists_open_dense_subset_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A → ∃ U, IsOpen U ∧ U ⊆ A ∧ closure U = closure A := by
  intro hP1
  refine ⟨interior A, isOpen_interior, interior_subset, ?_⟩
  exact (P1_iff_closure_interior_eq_closure).1 hP1

theorem open_iff_P1_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P1 A ↔ Topology.P3 A := by
  -- For an open set `A`, `P2 A` always holds.
  have hP2 : Topology.P2 A := P2_of_open hA
  constructor
  · intro _hP1
    -- Hence `P3 A` holds via `P3_of_P2`.
    exact P3_of_P2 hP2
  · intro _hP3 x hx
    -- Since `A` is open, `x ∈ interior A`.
    have hx_int : x ∈ interior A := by
      simpa [hA.interior_eq] using hx
    -- The closure contains its interior.
    exact subset_closure hx_int

theorem closed_iff_P2_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P2 A ↔ Topology.P3 A := by
  constructor
  · exact P3_of_P2
  · intro hP3
    intro x hx
    -- First, rewrite `P3` using the fact that `A` is closed.
    have hx_intA : x ∈ interior A := by
      have : x ∈ interior (closure A) := hP3 hx
      simpa [hA.closure_eq] using this
    -- Next, use monotonicity of `interior` to upgrade the membership.
    have hsubset : interior A ⊆ interior (closure (interior A)) := by
      have : interior (interior A) ⊆ interior (closure (interior A)) :=
        interior_mono (subset_closure : interior A ⊆ closure (interior A))
      simpa [interior_interior] using this
    exact hsubset hx_intA

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} : (∀ A ∈ 𝒜, Topology.P2 A) → Topology.P2 (⋃₀ 𝒜) := by
  intro hP2
  intro x hx
  -- Pick a set `A` in `𝒜` that contains `x`.
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  -- Apply `P2` to that particular set.
  have hP2A : Topology.P2 A := hP2 A hA_mem
  have hx_int : x ∈ interior (closure (interior A)) := hP2A hxA
  -- Relate the corresponding interiors/closures to those of `⋃₀ 𝒜`.
  have h_subset :
      interior (closure (interior A)) ⊆
        interior (closure (interior (⋃₀ 𝒜))) := by
    -- `A ⊆ ⋃₀ 𝒜`
    have h_sub : (A : Set X) ⊆ ⋃₀ 𝒜 := by
      intro y hy
      exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
    -- Monotonicity of `interior` and `closure`.
    have h_int_sub : interior A ⊆ interior (⋃₀ 𝒜) := interior_mono h_sub
    have h_cl_sub :
        closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) :=
      closure_mono h_int_sub
    exact interior_mono h_cl_sub
  exact h_subset hx_int

theorem exists_compact_subset_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A → ∃ K, IsCompact K ∧ K ⊆ A := by
  intro _
  refine ⟨(∅ : Set X), ?_⟩
  refine ⟨isCompact_empty, ?_⟩
  intro x hx
  cases hx

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} : (∀ A ∈ 𝒜, Topology.P1 A) → Topology.P1 (⋃₀ 𝒜) := by
  intro hP1 x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP1A : Topology.P1 A := hP1 A hA_mem
  have hx_cl : x ∈ closure (interior A) := hP1A hxA
  have h_subset : closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) := by
    have h_sub : (A : Set X) ⊆ ⋃₀ 𝒜 := by
      intro y hy
      exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
    have h_int_sub : interior A ⊆ interior (⋃₀ 𝒜) := interior_mono h_sub
    exact closure_mono h_int_sub
  exact h_subset hx_cl

theorem exists_dense_open_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P3 A → ∃ U, IsOpen U ∧ closure U = closure A := by
  intro hP3
  refine ⟨interior (closure (A : Set X)), isOpen_interior, ?_⟩
  -- Prove `closure (interior (closure A)) = closure A`
  apply subset_antisymm
  · -- `closure (interior (closure A)) ⊆ closure A`
    have h :
        closure (interior (closure A)) ⊆ closure (closure A) :=
      closure_mono
        (show interior (closure A) ⊆ closure A from interior_subset)
    simpa [closure_closure] using h
  · -- `closure A ⊆ closure (interior (closure A))`
    have h : (A : Set X) ⊆ interior (closure A) := hP3
    exact closure_mono h

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} : (∀ A ∈ 𝒜, Topology.P3 A) → Topology.P3 (⋃₀ 𝒜) := by
  intro hP3
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP3A : Topology.P3 A := hP3 A hA_mem
  have hx_int : x ∈ interior (closure A) := hP3A hxA
  have h_subset : interior (closure A) ⊆ interior (closure (⋃₀ 𝒜)) := by
    -- `A ⊆ ⋃₀ 𝒜`
    have h_sub : (A : Set X) ⊆ ⋃₀ 𝒜 := by
      intro y hy
      exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
    -- Apply monotonicity of `closure` and `interior`
    have h_cl_sub : closure A ⊆ closure (⋃₀ 𝒜) := closure_mono h_sub
    exact interior_mono h_cl_sub
  exact h_subset hx_int

theorem open_iff_P2_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A ↔ P3 A := by
  constructor
  · exact P3_of_P2
  · intro _hP3
    exact P2_of_open hA

theorem exists_closed_dense_subset_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : P3 A → ∃ K, IsClosed K ∧ A ⊆ K ∧ closure K = closure A := by
  intro _
  refine ⟨closure (A : Set X), isClosed_closure, subset_closure, ?_⟩
  simpa [closure_closure]

theorem P1_image_of_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : P1 A) (h : Homeomorph X Y) : P1 (h '' A) := by
  -- We must prove: `h '' A ⊆ closure (interior (h '' A))`.
  intro x hx
  -- Choose a preimage point `y : X` with `h y = x`.
  rcases hx with ⟨y, hyA, rfl⟩
  -- Using `P1 A`, `y` is in the closure of `interior A`.
  have hy_cl : y ∈ closure (interior (A : Set X)) := hA hyA
  -- We now show `h y ∈ closure (interior (h '' A))`.
  have : h y ∈ closure (interior (h '' A)) := by
    -- Use the neighbourhood formulation of the closure.
    apply (mem_closure_iff).2
    intro V hV_open hyV
    -- Pull back the neighbourhood under `h`.
    have hW_open : IsOpen (h ⁻¹' V) := hV_open.preimage h.continuous
    have hyW : y ∈ h ⁻¹' V := by
      simpa using hyV
    -- Since `y` is in the closure of `interior A`, `h ⁻¹' V` meets `interior A`.
    have h_nonempty :=
      (mem_closure_iff).1 hy_cl (h ⁻¹' V) hW_open hyW
    rcases h_nonempty with ⟨z, hzW, hz_intA⟩
    -- `hzW` gives `h z ∈ V`.
    have hzV : h z ∈ V := by
      simpa using hzW
    -- Show that `h z ∈ interior (h '' A)`.
    -- First, identify `h '' interior A` as a preimage by `h.symm` (hence open).
    have h_img_eq_preimage :
        (h '' interior A : Set _) = h.symm ⁻¹' interior A := by
      ext w
      constructor
      · rintro ⟨u, hu_int, rfl⟩
        simpa using hu_int
      · intro hw
        have : h.symm w ∈ interior A := hw
        exact
          ⟨h.symm w, this, by
            simpa using (h.apply_symm_apply w).symm⟩
    have hU_open : IsOpen (h '' interior A) := by
      have : IsOpen (h.symm ⁻¹' interior A) := by
        simpa using isOpen_interior.preimage h.symm.continuous
      simpa [h_img_eq_preimage] using this
    -- The image of `interior A` sits inside the image of `A`.
    have hU_subset : (h '' interior A : Set _) ⊆ h '' A := by
      rintro w ⟨u, hu_intA, rfl⟩
      exact ⟨u, interior_subset hu_intA, rfl⟩
    -- Hence `h '' interior A` is contained in the interior of `h '' A`.
    have hU_interior :
        (h '' interior A : Set _) ⊆ interior (h '' A) :=
      interior_maximal hU_subset hU_open
    -- Thus `h z` lies in that interior.
    have hz_int : h z ∈ interior (h '' A) := by
      have : h z ∈ (h '' interior A : Set _) := ⟨z, hz_intA, rfl⟩
      exact hU_interior this
    -- Produce a point in `V ∩ interior (h '' A)`.
    exact ⟨h z, And.intro hzV hz_int⟩
  exact this

theorem P2_image_of_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (h : Homeomorph X Y) : Topology.P2 A → Topology.P2 (h '' A) := by
  intro hP2
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` satisfies `P2 A`
  have hx_int : x ∈ interior (closure (interior A)) := hP2 hxA
  -- An open neighbourhood of `x`
  set U : Set X := interior (closure (interior A)) with hU_def
  have hU_open : IsOpen U := by
    dsimp [U] at *
    exact isOpen_interior
  have hxU : x ∈ U := by
    simpa [hU_def] using hx_int
  -- Define an open neighbourhood of `h x`
  let V : Set Y := h '' U
  have hV_open : IsOpen (V) := by
    -- rewrite `V` as a preimage by `h.symm`
    have h_eq : (V : Set Y) = h.symm ⁻¹' U := by
      dsimp [V]
      ext z
      constructor
      · rintro ⟨w, hwU, rfl⟩
        simpa using hwU
      · intro hz
        have : h.symm z ∈ U := hz
        exact ⟨h.symm z, this, by
          simpa using (h.apply_symm_apply z).symm⟩
    have : IsOpen (h.symm ⁻¹' U) := hU_open.preimage h.symm.continuous
    simpa [h_eq] using this
  have hxV : h x ∈ (V : Set Y) := by
    dsimp [V]
    exact ⟨x, hxU, rfl⟩
  --------------------------------------------------------------------------------
  --  Show that `V ⊆ closure (interior (h '' A))`
  --------------------------------------------------------------------------------
  have hV_subset : (V : Set Y) ⊆ closure (interior (h '' A)) := by
    intro z hz
    rcases hz with ⟨w, hwU, rfl⟩
    -- `U ⊆ closure (interior A)`
    have hU_subset : (U : Set X) ⊆ closure (interior A) := by
      have : interior (closure (interior A)) ⊆ closure (interior A) :=
        interior_subset
      simpa [hU_def] using this
    have hw_cl : w ∈ closure (interior A) := hU_subset hwU
    -- show `h w` belongs to `closure (h '' interior A)`
    have h_hw_cl : h w ∈ closure (h '' interior A) := by
      refine (mem_closure_iff).2 ?_
      intro W hW_open hwW
      -- pull back the neighbourhood via `h`
      have h_pre_open : IsOpen (h ⁻¹' W) := hW_open.preimage h.continuous
      have hw_pre : w ∈ h ⁻¹' W := by
        simpa using hwW
      have h_nonempty :=
        (mem_closure_iff).1 hw_cl (h ⁻¹' W) h_pre_open hw_pre
      rcases h_nonempty with ⟨u, ⟨hu_pre, hu_int⟩⟩
      refine ⟨h u, ?_⟩
      have huW : h u ∈ W := hu_pre
      have hu_img : h u ∈ h '' interior A := ⟨u, hu_int, rfl⟩
      exact And.intro huW hu_img
    -- relate closures using monotonicity
    have h_img_subset : (h '' interior A : Set Y) ⊆ interior (h '' A) := by
      -- first prove openness of the image
      have h_img_open : IsOpen (h '' interior A : Set Y) := by
        -- again rewrite as a preimage
        have h_eq : (h '' interior A : Set Y) = h.symm ⁻¹' interior A := by
          ext z
          constructor
          · rintro ⟨u, hu_int, rfl⟩
            simpa using hu_int
          · intro hz
            have : h.symm z ∈ interior A := hz
            exact ⟨h.symm z, this, by
              simpa using (h.apply_symm_apply z).symm⟩
        have : IsOpen (h.symm ⁻¹' interior A) :=
          (isOpen_interior).preimage h.symm.continuous
        simpa [h_eq] using this
      -- containment in `h '' A`
      have h_img_subset' : (h '' interior A : Set Y) ⊆ h '' A := by
        intro z hz
        rcases hz with ⟨u, hu_int, rfl⟩
        exact ⟨u, interior_subset hu_int, rfl⟩
      exact interior_maximal h_img_subset' h_img_open
    have h_closure_subset :
        closure (h '' interior A : Set Y) ⊆ closure (interior (h '' A)) :=
      closure_mono h_img_subset
    exact h_closure_subset h_hw_cl
  --------------------------------------------------------------------------------
  --  The required interior membership
  --------------------------------------------------------------------------------
  have hV_interior :
      (V : Set Y) ⊆ interior (closure (interior (h '' A))) :=
    interior_maximal hV_subset hV_open
  exact hV_interior hxV

theorem P3_image_of_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (h : Homeomorph X Y) : Topology.P3 A → Topology.P3 (h '' A) := by
  intro hP3
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  have hx_int : x ∈ interior (closure (A : Set X)) := hP3 hxA
  -- Define an open neighbourhood `U` of `x`.
  set U : Set X := interior (closure (A : Set X)) with hU_def
  have hU_open : IsOpen U := by
    dsimp [U] at *
    exact isOpen_interior
  have hxU : x ∈ U := by
    simpa [hU_def] using hx_int
  -- Take its image `V := h '' U`, an open neighbourhood of `h x`.
  let V : Set Y := h '' U
  have hV_open : IsOpen (V) := by
    -- rewrite `V` as a preimage of `U` by `h.symm`
    have h_eq : (V : Set Y) = h.symm ⁻¹' U := by
      dsimp [V]
      ext z
      constructor
      · rintro ⟨u, huU, rfl⟩
        simpa using huU
      · intro hz
        have : h.symm z ∈ U := hz
        exact ⟨h.symm z, this, by
          simpa using (h.apply_symm_apply z).symm⟩
    have : IsOpen (h.symm ⁻¹' U) := by
      have : IsOpen U := by
        simpa [hU_def] using hU_open
      exact this.preimage h.symm.continuous
    simpa [h_eq] using this
  have hyV : h x ∈ (V : Set Y) := by
    dsimp [V]
    exact ⟨x, hxU, rfl⟩
  --------------------------------------------------------------------------------
  --  Show: `V ⊆ closure (h '' A)`
  --------------------------------------------------------------------------------
  have hV_subset : (V : Set Y) ⊆ closure (h '' A) := by
    intro z hz
    rcases hz with ⟨w, hwU, rfl⟩
    -- We prove `h w ∈ closure (h '' A)` via the neighbourhood criterion.
    have : h w ∈ closure (h '' A) := by
      apply (mem_closure_iff).2
      intro W hW_open hwW
      -- pull back the neighbourhood via `h`
      have hW_pre_open : IsOpen (h ⁻¹' W) := hW_open.preimage h.continuous
      have hw_pre : w ∈ h ⁻¹' W := by
        simpa using hwW
      -- `w ∈ U ⊆ interior (closure A) ⊆ closure A`
      have hw_closureA : w ∈ closure (A : Set X) := by
        have : w ∈ interior (closure (A : Set X)) := by
          simpa [hU_def] using hwU
        exact interior_subset this
      -- Use density of `A` near `w`.
      have h_nonempty :=
        (mem_closure_iff).1 hw_closureA (h ⁻¹' W) hW_pre_open hw_pre
      rcases h_nonempty with ⟨t, ht_pre, htA⟩
      -- `t ∈ A` and `h t ∈ W`.
      exact
        ⟨h t, by
          have htW : h t ∈ W := ht_pre
          have ht_image : h t ∈ h '' A := ⟨t, htA, rfl⟩
          exact And.intro htW ht_image⟩
    exact this
  -- Since `V` is open and contained in the closure, it is contained in the interior of the closure.
  have hV_subset_int :
      (V : Set Y) ⊆ interior (closure (h '' A)) :=
    interior_maximal hV_subset hV_open
  exact hV_subset_int hyV

theorem P1_of_open_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) (h_dense : closure A = Set.univ) : Topology.P1 A := by
  intro x hx
  simpa [hA.interior_eq, h_dense] using (Set.mem_univ x)

theorem P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 (interior A) := by
  intro x hx
  -- First, view `hx` as a membership in `interior (interior A)`.
  have hx₁ : x ∈ interior (interior A) := by
    simpa [interior_interior] using hx
  -- `interior (interior A)` is included in `interior (closure (interior A))`.
  have h_subset :
      interior (interior A) ⊆ interior (closure (interior A)) := by
    have : (interior A : Set X) ⊆ closure (interior A) := subset_closure
    exact interior_mono this
  -- Apply this inclusion.
  have hx₂ : x ∈ interior (closure (interior A)) := h_subset hx₁
  -- Re-express the target set via `interior_interior`.
  simpa [interior_interior] using hx₂

theorem P3_image_of_open_map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {f : X → Y} (hf : IsOpenMap f) (hcont : Continuous f) : Topology.P3 A → Topology.P3 (f '' A) := by
  intro hP3
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` lies in the interior of `closure A`
  have hx_int : x ∈ interior (closure (A : Set X)) := hP3 hxA
  -- Define `U := interior (closure A)`
  let U : Set X := interior (closure (A : Set X))
  have hU_open : IsOpen U := by
    dsimp [U]
    exact isOpen_interior
  have hxU : x ∈ U := by
    dsimp [U] at *
    simpa using hx_int
  -- Define `V := f '' U`
  let V : Set Y := f '' U
  have hV_open : IsOpen V := by
    dsimp [V]
    exact hf _ hU_open
  have hyV : (f x) ∈ V := by
    dsimp [V]
    exact ⟨x, hxU, rfl⟩
  ------------------------------------------------------------------
  --  Show that `V ⊆ closure (f '' A)`
  ------------------------------------------------------------------
  have hV_subset : (V : Set Y) ⊆ closure (f '' A) := by
    intro z hz
    rcases hz with ⟨w, hwU, rfl⟩
    -- `w ∈ closure A`
    have hw_clA : w ∈ closure (A : Set X) := by
      -- `U ⊆ closure A`
      have hU_subset : (U : Set X) ⊆ closure (A : Set X) := by
        dsimp [U]
        exact interior_subset
      exact hU_subset hwU
    -- Use continuity to send closures
    have : f w ∈ closure (f '' A) := by
      apply (mem_closure_iff).2
      intro W hW_open hfwinW
      -- Preimage of `W`
      have h_preopen : IsOpen (f ⁻¹' W) := hW_open.preimage hcont
      have hw_pre : w ∈ f ⁻¹' W := by
        simpa using hfwinW
      rcases (mem_closure_iff).1 hw_clA _ h_preopen hw_pre with
        ⟨u, ⟨hu_pre, huA⟩⟩
      refine ⟨f u, ?_⟩
      have hfuW : f u ∈ W := by
        simpa using hu_pre
      have hfuA : f u ∈ f '' A := ⟨u, huA, rfl⟩
      exact And.intro hfuW hfuA
    simpa using this
  ------------------------------------------------------------------
  --  Since `V` is open, it is contained in the interior of the closure.
  ------------------------------------------------------------------
  have hV_subset_int : (V : Set Y) ⊆ interior (closure (f '' A)) :=
    interior_maximal hV_subset hV_open
  exact hV_subset_int hyV

theorem P1_empty {X : Type*} [TopologicalSpace X] : Topology.P1 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P2_empty {X : Type*} [TopologicalSpace X] : Topology.P2 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P3_empty {X : Type*} [TopologicalSpace X] : Topology.P3 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P3_univ {X : Type*} [TopologicalSpace X] : Topology.P3 (Set.univ : Set X) := by
  intro x hx
  simpa [closure_univ, interior_univ] using hx

theorem P2_univ {X : Type*} [TopologicalSpace X] : Topology.P2 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using (Set.mem_univ x)

theorem open_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P1 A := by
  intro x hx
  have : x ∈ closure A := subset_closure hx
  simpa [hA.interior_eq] using this

theorem P2_of_union_dense {X : Type*} [TopologicalSpace X] {A B : Set X} : closure (interior B) = Set.univ → P2 (A ∪ B) := by
  intro h_dense
  -- First, compute that `interior (closure (interior (A ∪ B))) = univ`.
  have h_int_univ :
      interior (closure (interior (A ∪ B))) = (Set.univ : Set X) := by
    -- Show that the corresponding closure is the whole space.
    have h_closure_univ :
        closure (interior (A ∪ B)) = (Set.univ : Set X) := by
      -- `interior B ⊆ interior (A ∪ B)`
      have h_subset : (interior B : Set X) ⊆ interior (A ∪ B) := by
        have : (B : Set X) ⊆ A ∪ B := by
          intro y hy
          exact Or.inr hy
        exact interior_mono this
      -- Taking closures preserves the inclusion.
      have h_closure_subset :
          closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h_subset
      -- Use the hypothesis `closure (interior B) = univ`.
      have h_univ_subset :
          (Set.univ : Set X) ⊆ closure (interior (A ∪ B)) := by
        simpa [h_dense] using h_closure_subset
      -- Deduce equality via `subset_antisymm`.
      apply Set.Subset.antisymm
      · intro y hy; trivial
      · exact h_univ_subset
    -- Taking interiors, we still get `univ`.
    simpa [h_closure_univ, interior_univ]
  -- Now prove `P2 (A ∪ B)`.
  intro x hx
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [h_int_univ] using this

theorem open_of_P2_closed {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → Topology.P2 A → IsOpen A := by
  intro hClosed hP2
  exact open_of_closed_and_P3 hClosed (P3_of_P2 hP2)

theorem exists_clopen_subset_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A → ∃ U, IsOpen U ∧ IsClosed U ∧ U ⊆ A := by
  intro _
  exact ⟨(∅ : Set X), isOpen_empty, isClosed_empty, Set.empty_subset _⟩

theorem P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P1 A) : Topology.P1 (closure A) := by
  intro x hx
  -- `P1 A` yields `closure A ⊆ closure (interior A)`.
  have h₁ : closure (A : Set X) ⊆ closure (interior A) := by
    -- First enlarge with `closure_mono`, then simplify.
    have : closure (A : Set X) ⊆ closure (closure (interior A)) :=
      closure_mono hA
    simpa [closure_closure] using this
  have hx₁ : x ∈ closure (interior A) := h₁ hx
  -- We also have `interior A ⊆ interior (closure A)`.
  have h₂ : interior A ⊆ interior (closure A) := by
    have h_subset : (A : Set X) ⊆ closure A := subset_closure
    exact interior_mono h_subset
  -- Taking closures preserves this inclusion.
  have h₃ :
      closure (interior A) ⊆ closure (interior (closure A)) :=
    closure_mono h₂
  exact h₃ hx₁

theorem P1_compl_of_P3_closed {X : Type*} [TopologicalSpace X] {A : Set X} (h_closed : IsClosed A) (hP3 : Topology.P3 A) : Topology.P1 Aᶜ := by
  have hOpen : IsOpen (Aᶜ) := h_closed.isOpen_compl
  exact open_implies_P1 hOpen

theorem P2_of_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (h1 : Topology.P1 A) (h3 : Topology.P3 A) : Topology.P2 A := by
  exact P1_and_P3_implies_P2 ⟨h1, h3⟩

theorem P1_prod {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P1 A) (hB : P1 B) : P1 (A ×ˢ B) := by
  intro p hp
  -- Decompose the membership in the product set.
  rcases hp with ⟨hpA, hpB⟩
  -- Use `P1` on each coordinate.
  have hx : p.1 ∈ closure (interior A) := hA hpA
  have hy : p.2 ∈ closure (interior B) := hB hpB
  --------------------------------------------------------------------------------
  -- Step 1. `p` lies in the closure of `interior A ×ˢ interior B`.
  --------------------------------------------------------------------------------
  have h_mem :
      p ∈ closure ((interior A) ×ˢ (interior B) : Set (X × Y)) := by
    -- Rely on `closure_prod_eq`.
    have : p ∈ (closure (interior A) ×ˢ closure (interior B) : Set (X × Y)) :=
      ⟨hx, hy⟩
    simpa [closure_prod_eq] using this
  --------------------------------------------------------------------------------
  -- Step 2. Relate the two closures.
  --------------------------------------------------------------------------------
  have h_subset :
      closure ((interior A) ×ˢ (interior B) : Set (X × Y))
        ⊆ closure (interior (A ×ˢ B)) := by
    -- First show that `interior A ×ˢ interior B ⊆ interior (A ×ˢ B)`.
    have h_interior_subset :
        ((interior A) ×ˢ (interior B) : Set (X × Y))
          ⊆ interior (A ×ˢ B) := by
      -- It is an open subset of `A ×ˢ B`.
      have h_basic :
          ((interior A) ×ˢ (interior B) : Set (X × Y)) ⊆ (A ×ˢ B) := by
        intro q hq
        rcases hq with ⟨hqx, hqy⟩
        exact And.intro (interior_subset hqx) (interior_subset hqy)
      have h_open :
          IsOpen ((interior A) ×ˢ (interior B) : Set (X × Y)) :=
        isOpen_interior.prod isOpen_interior
      exact interior_maximal h_basic h_open
    -- Taking closures preserves inclusions.
    exact closure_mono h_interior_subset
  --------------------------------------------------------------------------------
  -- Step 3. Conclude.
  --------------------------------------------------------------------------------
  exact h_subset h_mem

theorem P3_prod {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P3 A) (hB : P3 B) : P3 (A ×ˢ B) := by
  intro p hp
  -- Decompose the membership in the product set.
  rcases hp with ⟨hpA, hpB⟩
  -- Apply `P3` on each coordinate.
  have hx : p.1 ∈ interior (closure (A : Set X)) := hA hpA
  have hy : p.2 ∈ interior (closure (B : Set Y)) := hB hpB
  -- Consider the open neighbourhood `U ×ˢ V` of `p`.
  let U : Set X := interior (closure (A : Set X))
  let V : Set Y := interior (closure (B : Set Y))
  have hU_open : IsOpen U := isOpen_interior
  have hV_open : IsOpen V := isOpen_interior
  have hUV_open : IsOpen (U ×ˢ V : Set (X × Y)) := hU_open.prod hV_open
  have hpUV : p ∈ (U ×ˢ V : Set (X × Y)) := by
    dsimp [U, V] at *
    exact And.intro hx hy
  -- Show that `U ×ˢ V ⊆ closure (A ×ˢ B)`.
  have h_subset_closure : (U ×ˢ V : Set (X × Y)) ⊆ closure (A ×ˢ B) := by
    intro q hq
    rcases hq with ⟨hqU, hqV⟩
    -- Points of `U` (resp. `V`) lie in `closure A` (resp. `closure B`).
    have hq1 : q.1 ∈ closure (A : Set X) := interior_subset hqU
    have hq2 : q.2 ∈ closure (B : Set Y) := interior_subset hqV
    have : (q : X × Y) ∈ (closure A ×ˢ closure B : Set (X × Y)) :=
      And.intro hq1 hq2
    -- Use `closure_prod_eq` to convert.
    simpa [closure_prod_eq] using this
  -- Hence `U ×ˢ V ⊆ interior (closure (A ×ˢ B))`.
  have h_subset_int :
      (U ×ˢ V : Set (X × Y)) ⊆ interior (closure (A ×ˢ B)) :=
    interior_maximal h_subset_closure hUV_open
  -- Conclude for `p`.
  exact h_subset_int hpUV

theorem P2_prod {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P2 A) (hB : Topology.P2 B) : Topology.P2 (A ×ˢ B) := by
  intro p hp
  rcases hp with ⟨hpA, hpB⟩
  -- Use `P2` on each coordinate.
  have hx : p.1 ∈ interior (closure (interior A)) := hA hpA
  have hy : p.2 ∈ interior (closure (interior B)) := hB hpB
  -- Define suitable open neighbourhoods.
  let U : Set X := interior (closure (interior A))
  let V : Set Y := interior (closure (interior B))
  have hU_open : IsOpen U := isOpen_interior
  have hV_open : IsOpen V := isOpen_interior
  have hUV_open : IsOpen (U ×ˢ V : Set (X × Y)) := hU_open.prod hV_open
  have hpUV : p ∈ (U ×ˢ V : Set (X × Y)) := by
    dsimp [U, V] at *
    exact And.intro hx hy
  --------------------------------------------------------------------
  --  Show `U ×ˢ V ⊆ closure (interior (A ×ˢ B))`.
  --------------------------------------------------------------------
  have h_subset_closure :
      (U ×ˢ V : Set (X × Y)) ⊆ closure (interior (A ×ˢ B)) := by
    intro q hq
    rcases hq with ⟨hqU, hqV⟩
    -- Upgrade to closures of the interiors.
    have hq1 : q.1 ∈ closure (interior A) := interior_subset hqU
    have hq2 : q.2 ∈ closure (interior B) := interior_subset hqV
    have hq_prod :
        (q : X × Y) ∈
          (closure (interior A) ×ˢ closure (interior B) : Set (X × Y)) :=
      And.intro hq1 hq2
    -- Rewrite with `closure_prod_eq`.
    have hq_cl :
        (q : X × Y) ∈
          closure ((interior A) ×ˢ (interior B) : Set (X × Y)) := by
      simpa [closure_prod_eq] using hq_prod
    -- `interior A ×ˢ interior B ⊆ interior (A ×ˢ B)`.
    have h_interior_subset :
        ((interior A) ×ˢ (interior B) : Set (X × Y)) ⊆
          interior (A ×ˢ B) := by
      -- Basic inclusion.
      have h_basic :
          ((interior A) ×ˢ (interior B) : Set (X × Y)) ⊆ (A ×ˢ B) := by
        intro r hr
        rcases hr with ⟨hrA, hrB⟩
        exact And.intro (interior_subset hrA) (interior_subset hrB)
      -- Openness of the product.
      have h_open :
          IsOpen ((interior A) ×ˢ (interior B) : Set (X × Y)) :=
        isOpen_interior.prod isOpen_interior
      exact interior_maximal h_basic h_open
    -- Taking closures preserves inclusions.
    have h_closure_subset :
        closure ((interior A) ×ˢ (interior B) : Set (X × Y)) ⊆
          closure (interior (A ×ˢ B)) :=
      closure_mono h_interior_subset
    exact h_closure_subset hq_cl
  --------------------------------------------------------------------
  --  Since `U ×ˢ V` is open, it is contained in the interior
  --  of the above closure.
  --------------------------------------------------------------------
  have h_subset_int :
      (U ×ˢ V : Set (X × Y)) ⊆
        interior (closure (interior (A ×ˢ B))) :=
    interior_maximal h_subset_closure hUV_open
  exact h_subset_int hpUV

theorem P1_univ {X : Type*} [TopologicalSpace X] : Topology.P1 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 (interior A) := by
  simpa using (P1_of_P2 (A := interior A) P2_interior)

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P3 (interior A) := by
  simpa using P3_of_P2 (A := interior A) P2_interior

theorem P2_iff_P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = closure A) : Topology.P2 A ↔ Topology.P3 A := by
  -- First, turn the hypothesis into `P1 A`.
  have hP1 : Topology.P1 A :=
    (P1_iff_closure_interior_eq_closure (A := A)).2 h
  -- Now establish the equivalence between `P2 A` and `P3 A`.
  constructor
  · intro hP2
    exact P1_and_P2_implies_P3 (A := A) ⟨hP1, hP2⟩
  · intro hP3
    exact P1_and_P3_implies_P2 (A := A) ⟨hP1, hP3⟩

theorem subset_closure_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P2 A) : A ⊆ closure (interior A) := by
  intro x hx
  exact interior_subset (h hx)

theorem closure_interior_eq_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P2 A) : closure (interior A) = closure (interior (closure A)) := by
  -- First, derive `P1 A` from the given `P2 A`.
  have hP1 : P1 A := P1_of_P2 h
  ------------------------------------------------------------------
  -- 1.  `closure (interior A) ⊆ closure (interior (closure A))`
  ------------------------------------------------------------------
  have h_left : closure (interior A) ⊆ closure (interior (closure A)) := by
    -- Since `interior A ⊆ interior (closure A)`, taking closures yields the claim.
    have h_sub : interior A ⊆ interior (closure (A : Set X)) := by
      have : (A : Set X) ⊆ closure A := subset_closure
      exact interior_mono this
    exact closure_mono h_sub
  ------------------------------------------------------------------
  -- 2.  `closure (interior (closure A)) ⊆ closure (interior A)`
  ------------------------------------------------------------------
  -- First, show the corresponding inclusion for the interiors themselves.
  have h_sub : interior (closure (A : Set X)) ⊆ closure (interior A) := by
    intro x hx
    -- `hx` puts `x` inside `closure A`.
    have hx_cl : x ∈ closure (A : Set X) := interior_subset hx
    -- `P1 A` gives the needed inclusion on closures.
    have h_closure_subset : closure (A : Set X) ⊆ closure (interior A) := by
      -- `closure_mono hP1` yields
      --   `closure A ⊆ closure (closure (interior A))`.
      -- Collapse the double closure on the right.
      have : closure (A : Set X) ⊆ closure (closure (interior A)) :=
        closure_mono hP1
      simpa [closure_closure] using this
    exact h_closure_subset hx_cl
  -- Now, take closures and use `closure_minimal`.
  have h_right : closure (interior (closure (A : Set X))) ⊆
      closure (interior A) := by
    apply closure_minimal h_sub
    exact isClosed_closure
  ------------------------------------------------------------------
  -- 3.  Conclude with antisymmetry.
  ------------------------------------------------------------------
  exact Set.Subset.antisymm h_left h_right

theorem P3_of_local_closure_neighborhoods {X : Type*} [TopologicalSpace X] {A : Set X} (h : ∀ x ∈ A, ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ closure A) : Topology.P3 A := by
  intro x hxA
  rcases h x hxA with ⟨U, hU_open, hxU, hU_subset⟩
  have hU_int : (U : Set X) ⊆ interior (closure (A : Set X)) :=
    interior_maximal hU_subset hU_open
  exact hU_int hxU

theorem P2_of_local_double_closure_neighborhoods {X : Type*} [TopologicalSpace X] {A : Set X} (h : ∀ x ∈ A, ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ closure (interior A)) : Topology.P2 A := by
  intro x hxA
  rcases h x hxA with ⟨U, hU_open, hxU, hU_subset⟩
  have hU_int : (U : Set X) ⊆ interior (closure (interior A)) :=
    interior_maximal hU_subset hU_open
  exact hU_int hxU

theorem P2_Union_of_chain {X : Type*} [TopologicalSpace X] {ι : Type*} {F : ι → Set X} (hchain : ∀ i j, F i ⊆ F j ∨ F j ⊆ F i) (hF : ∀ i, Topology.P2 (F i)) : Topology.P2 (⋃ i, F i) := by
  exact P2_Union (F := F) hF

theorem P1_sdiff {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P1 A) (hB : IsClosed B) : Topology.P1 (A \ B) := by
  intro x hx
  -- Decompose the membership in `A \ B`.
  have hxA : x ∈ A := hx.1
  have hx_notB : x ∈ (Bᶜ : Set X) := by
    -- `hx.2 : x ∉ B`, which is definitionally `x ∈ Bᶜ`.
    simpa using hx.2
  -- We show that every neighbourhood of `x` meets `interior (A \ B)`.
  apply (mem_closure_iff).2
  intro V hV_open hxV
  -- Intersect the neighbourhood with `Bᶜ`, still an open neighbourhood of `x`.
  have hW_open : IsOpen (V ∩ (Bᶜ : Set X)) :=
    hV_open.inter hB.isOpen_compl
  have hxW : x ∈ V ∩ (Bᶜ : Set X) := And.intro hxV hx_notB
  -- Since `x ∈ closure (interior A)`, this set meets `interior A`.
  have hx_clA : x ∈ closure (interior A) := hA hxA
  rcases
      (mem_closure_iff).1 hx_clA _ hW_open hxW with
    ⟨y, hyW, hy_intA⟩
  -- Extract the two facts `y ∈ V` and `y ∈ Bᶜ`.
  have hyV : y ∈ V := hyW.1
  have hy_notB : y ∈ (Bᶜ : Set X) := hyW.2
  -- Show that `y` actually belongs to `interior (A \ B)`.
  have hy_int_diff : y ∈ interior (A \ B) := by
    -- The open set `interior A ∩ Bᶜ` sits inside `A \ B`.
    have h_subset :
        (interior A ∩ (Bᶜ : Set X) : Set X) ⊆ interior (A \ B) := by
      -- Basic inclusion into `A \ B`.
      have h_basic :
          (interior A ∩ (Bᶜ : Set X) : Set X) ⊆ (A \ B) := by
        intro z hz
        exact And.intro (interior_subset hz.1) hz.2
      -- Openness of the set.
      have h_open :
          IsOpen ((interior A) ∩ (Bᶜ : Set X) : Set X) :=
        (isOpen_interior.inter hB.isOpen_compl)
      -- Apply the maximality property of `interior`.
      exact interior_maximal h_basic h_open
    have hy_mem : y ∈ (interior A ∩ (Bᶜ : Set X)) := And.intro hy_intA hy_notB
    exact h_subset hy_mem
  -- Provide the desired witness in `V ∩ interior (A \ B)`.
  exact ⟨y, And.intro hyV hy_int_diff⟩

theorem P3_exists_open_dense {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P3 A → ∃ U, IsOpen U ∧ closure U ⊆ closure A ∧ interior (closure A) ⊆ closure U := by
  intro _hP3
  refine ⟨interior (closure (A : Set X)), isOpen_interior, ?_, ?_⟩
  · -- `closure U ⊆ closure A`
    have h_subset :
        (interior (closure (A : Set X)) : Set X) ⊆ closure A :=
      interior_subset
    -- Taking closures preserves inclusions.
    have h_closure :
        closure (interior (closure (A : Set X))) ⊆ closure A := by
      simpa [closure_closure] using (closure_mono h_subset)
    exact h_closure
  · -- `interior (closure A) ⊆ closure U`
    intro x hx
    exact subset_closure hx

theorem P1_iff {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A ↔ (∀ x, x ∉ closure (interior A) → x ∉ A) := by
  classical
  constructor
  · intro hP1 x hx_not hxA
    have hx_cl : x ∈ closure (interior (A : Set X)) := hP1 hxA
    exact hx_not hx_cl
  · intro hCond x hxA
    have hx_cl : x ∈ closure (interior (A : Set X)) := by
      by_cases hmem : x ∈ closure (interior (A : Set X))
      · exact hmem
      · have h_notA : x ∉ A := hCond x hmem
        exact (False.elim (h_notA hxA))
    exact hx_cl

theorem exists_closure_subset_open_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P1 A) : ∃ U, IsOpen U ∧ closure U ⊆ closure A ∧ A ⊆ closure U := by
  refine ⟨interior A, isOpen_interior, ?_, ?_⟩
  ·
    have : closure (interior A : Set X) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    simpa using this
  ·
    simpa using hA

theorem P1_prod_univ {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y] {A : Set X} (hA : Topology.P1 A) : Topology.P1 (A ×ˢ (Set.univ : Set Y)) := by
  have hUniv : Topology.P1 (Set.univ : Set Y) := P1_univ
  simpa using P1_prod (A := A) (B := (Set.univ : Set Y)) hA hUniv

theorem P1_Union_finite {X : Type*} [TopologicalSpace X] {F : Finset (Set X)} (hF : ∀ A, A ∈ F → Topology.P1 A) : Topology.P1 (⋃ A ∈ F, A) := by
  classical
  revert hF
  induction F using Finset.induction with
  | empty =>
      intro _hF
      simpa using (P1_empty : Topology.P1 (∅ : Set X))
  | @insert A s hA_notin_s ih =>
      intro hF
      -- `P1` for the distinguished set `A`
      have hA : Topology.P1 A := by
        have : (A : Set X) ∈ (insert A s : Finset (Set X)) :=
          Finset.mem_insert_self A s
        exact hF A this
      -- `P1` for the union over the remaining sets, from the induction hypothesis
      have hF' : ∀ B, B ∈ s → Topology.P1 B := by
        intro B hB
        exact hF B (Finset.mem_insert_of_mem hB)
      have h_s : Topology.P1 (⋃ B ∈ s, (B : Set X)) := ih hF'
      -- Combine the two using `P1_union`
      have h_union : Topology.P1 (A ∪ ⋃ B ∈ s, (B : Set X)) :=
        P1_union hA h_s
      -- Relate the two ways of writing the union
      have h_eq :
          (⋃ B ∈ (insert A s : Finset (Set X)), (B : Set X)) =
            (A ∪ ⋃ B ∈ s, (B : Set X)) := by
        ext x
        constructor
        · intro hx
          rcases Set.mem_iUnion.1 hx with ⟨B, hx₁⟩
          rcases Set.mem_iUnion.1 hx₁ with ⟨hBmem, hxB⟩
          have h_cases : (B : Set X) = A ∨ (B : Set X) ∈ s :=
            (Finset.mem_insert).1 hBmem
          cases h_cases with
          | inl hBA =>
              left
              simpa [hBA] using hxB
          | inr hBinS =>
              right
              have : x ∈ ⋃ B ∈ s, (B : Set X) := by
                apply Set.mem_iUnion.2
                refine ⟨B, ?_⟩
                apply Set.mem_iUnion.2
                exact ⟨hBinS, hxB⟩
              exact this
        · intro hx
          cases hx with
          | inl hxA =>
              apply Set.mem_iUnion.2
              refine ⟨A, ?_⟩
              apply Set.mem_iUnion.2
              exact ⟨Finset.mem_insert_self A s, hxA⟩
          | inr hxUnion =>
              rcases Set.mem_iUnion.1 hxUnion with ⟨B, hx₁⟩
              rcases Set.mem_iUnion.1 hx₁ with ⟨hBmem, hxB⟩
              apply Set.mem_iUnion.2
              refine ⟨B, ?_⟩
              apply Set.mem_iUnion.2
              exact ⟨Finset.mem_insert_of_mem hBmem, hxB⟩
      simpa [h_eq] using h_union

theorem P3_sdiff {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P3 A) (hB : IsClosed B) : Topology.P3 (A \ B) := by
  intro x hx
  -- Split the membership information.
  have hxA : x ∈ A := hx.1
  have hx_notB : x ∈ (Bᶜ : Set X) := by
    simpa using hx.2
  -- From `P3 A`, `x` lies in the interior of the closure of `A`.
  have hx_int : x ∈ interior (closure (A : Set X)) := hA hxA
  -- Define `U := interior (closure A)`.
  let U : Set X := interior (closure (A : Set X))
  have hU_open : IsOpen U := isOpen_interior
  have hxU : x ∈ U := by
    dsimp [U] at *
    exact hx_int
  -- Define `V := U ∩ Bᶜ`, an open neighbourhood of `x`.
  let V : Set X := U ∩ (Bᶜ : Set X)
  have hV_open : IsOpen V := hU_open.inter hB.isOpen_compl
  have hxV : x ∈ V := by
    dsimp [V] at *
    exact And.intro hxU hx_notB
  -- Show `V ⊆ closure (A \ B)`.
  have hV_subset : (V : Set X) ⊆ closure (A \ B) := by
    intro y hyV
    have hyU : y ∈ U := hyV.1
    have hy_notB : y ∈ (Bᶜ : Set X) := hyV.2
    -- `y` belongs to `closure A`.
    have hy_clA : y ∈ closure (A : Set X) := by
      have : (U : Set X) ⊆ closure A := interior_subset
      exact this hyU
    -- Use the neighbourhood criterion for the closure.
    have : y ∈ closure (A \ B) := by
      apply (mem_closure_iff).2
      intro W hW_open hyW
      -- Shrink the neighbourhood inside `Bᶜ`.
      have hW'_open : IsOpen (W ∩ (Bᶜ : Set X)) :=
        hW_open.inter hB.isOpen_compl
      have hyW' : y ∈ W ∩ (Bᶜ : Set X) := And.intro hyW hy_notB
      -- Since `y ∈ closure A`, this set meets `A`.
      rcases
          (mem_closure_iff).1 hy_clA _ hW'_open hyW' with
        ⟨z, hzW', hzA⟩
      have hzW : z ∈ W := hzW'.1
      have hz_notB : z ∈ (Bᶜ : Set X) := hzW'.2
      have hz_diff : z ∈ A \ B := And.intro hzA hz_notB
      exact ⟨z, And.intro hzW hz_diff⟩
    exact this
  -- `V` is open and contained in the desired closure, hence in its interior.
  have hV_subset_int :
      (V : Set X) ⊆ interior (closure (A \ B)) :=
    interior_maximal hV_subset hV_open
  -- Conclude that `x` lies in the required interior.
  exact hV_subset_int hxV

theorem P3_Union_finite {X : Type*} [TopologicalSpace X] {F : Finset (Set X)} : (∀ A ∈ F, Topology.P3 A) → Topology.P3 (⋃ A ∈ F, A) := by
  classical
  revert F
  intro F
  induction F using Finset.induction with
  | empty =>
      intro _hP3
      simpa using (P3_empty : Topology.P3 (∅ : Set X))
  | @insert A s hA_notin_s ih =>
      intro hF
      -- `P3` for the distinguished set `A`
      have hA : Topology.P3 A := by
        have : (A : Set X) ∈ (insert A s : Finset (Set X)) :=
          Finset.mem_insert_self A s
        exact hF A this
      -- `P3` for the union over the remaining sets, from the induction hypothesis
      have hF' : ∀ B, B ∈ s → Topology.P3 B := by
        intro B hB
        exact hF B (Finset.mem_insert_of_mem hB)
      have h_s : Topology.P3 (⋃ B ∈ s, (B : Set X)) := ih hF'
      -- Combine the two using a bespoke `P3`-union argument
      have h_union : Topology.P3 (A ∪ ⋃ B ∈ s, (B : Set X)) := by
        intro x hx
        cases hx with
        | inl hxA =>
            -- Case `x ∈ A`
            have hx_int : x ∈ interior (closure (A : Set X)) := hA hxA
            -- Monotonicity
            have hsubset :
                interior (closure (A : Set X)) ⊆
                  interior (closure (A ∪ ⋃ B ∈ s, (B : Set X))) := by
              apply interior_mono
              apply closure_mono
              intro y hy
              exact Or.inl hy
            exact hsubset hx_int
        | inr hxU =>
            -- Case `x` lies in the big union over `s`
            have hx_int : x ∈
                interior (closure (⋃ B ∈ s, (B : Set X))) := h_s hxU
            have hsubset :
                interior (closure (⋃ B ∈ s, (B : Set X))) ⊆
                  interior (closure (A ∪ ⋃ B ∈ s, (B : Set X))) := by
              apply interior_mono
              apply closure_mono
              intro y hy
              exact Or.inr hy
            exact hsubset hx_int
      -- Relate the two ways of writing the union
      have h_eq :
          (⋃ B ∈ (insert A s : Finset (Set X)), (B : Set X)) =
            (A ∪ ⋃ B ∈ s, (B : Set X)) := by
        ext x
        constructor
        · intro hx
          rcases Set.mem_iUnion.1 hx with ⟨B, hx₁⟩
          rcases Set.mem_iUnion.1 hx₁ with ⟨hBmem, hxB⟩
          have h_cases : (B : Set X) = A ∨ (B : Set X) ∈ s :=
            (Finset.mem_insert).1 hBmem
          cases h_cases with
          | inl hBA =>
              left
              simpa [hBA] using hxB
          | inr hBinS =>
              right
              have : x ∈ ⋃ B ∈ s, (B : Set X) := by
                apply Set.mem_iUnion.2
                exact ⟨B, Set.mem_iUnion.2 ⟨hBinS, hxB⟩⟩
              exact this
        · intro hx
          cases hx with
          | inl hxA =>
              apply Set.mem_iUnion.2
              exact ⟨A, Set.mem_iUnion.2
                    ⟨Finset.mem_insert_self _ _, hxA⟩⟩
          | inr hxUnion =>
              rcases Set.mem_iUnion.1 hxUnion with ⟨B, hx₁⟩
              rcases Set.mem_iUnion.1 hx₁ with ⟨hBmem, hxB⟩
              apply Set.mem_iUnion.2
              exact ⟨B, Set.mem_iUnion.2
                    ⟨Finset.mem_insert_of_mem hBmem, hxB⟩⟩
      simpa [h_eq] using h_union

theorem P1_bUnion {X : Type*} [TopologicalSpace X] {ι : Type*} {F : ι → Set X} (s : Finset ι) (hF : ∀ i ∈ s, Topology.P1 (F i)) : Topology.P1 (⋃ i ∈ s, F i) := by
  classical
  revert hF
  induction s using Finset.induction with
  | empty =>
      intro _hF
      simpa using (P1_empty : Topology.P1 (∅ : Set X))
  | @insert i s hi_notin_s ih =>
      intro hF
      -- `P1` for the distinguished index `i`
      have hFi : Topology.P1 (F i) :=
        hF i (Finset.mem_insert_self _ _)
      -- `P1` for the remaining indices, by induction hypothesis
      have hRest : Topology.P1 (⋃ j ∈ s, F j) :=
        ih (by
          intro j hj
          exact hF j (Finset.mem_insert_of_mem hj))
      -- Combine the two using `P1_union`
      have h_union : Topology.P1 (F i ∪ ⋃ j ∈ s, F j) :=
        P1_union hFi hRest
      -- Relate the two ways of writing the union
      have h_eq :
          (⋃ j ∈ (insert i s : Finset ι), F j : Set X) =
            (F i ∪ ⋃ j ∈ s, F j) := by
        ext x
        constructor
        · intro hx
          rcases Set.mem_iUnion.1 hx with ⟨j, hx₁⟩
          rcases Set.mem_iUnion.1 hx₁ with ⟨hjmem, hxj⟩
          have h_cases : j = i ∨ j ∈ s := (Finset.mem_insert).1 hjmem
          cases h_cases with
          | inl hji =>
              left
              simpa [hji] using hxj
          | inr hjs =>
              right
              have : x ∈ ⋃ j ∈ s, F j := by
                apply Set.mem_iUnion.2
                exact ⟨j, Set.mem_iUnion.2 ⟨hjs, hxj⟩⟩
              exact this
        · intro hx
          cases hx with
          | inl hxi =>
              apply Set.mem_iUnion.2
              exact ⟨i, Set.mem_iUnion.2 ⟨Finset.mem_insert_self _ _, hxi⟩⟩
          | inr hxrest =>
              rcases Set.mem_iUnion.1 hxrest with ⟨j, hx₁⟩
              rcases Set.mem_iUnion.1 hx₁ with ⟨hjs, hxj⟩
              apply Set.mem_iUnion.2
              exact ⟨j, Set.mem_iUnion.2 ⟨Finset.mem_insert_of_mem hjs, hxj⟩⟩
      simpa [h_eq] using h_union

theorem P3_exists_dense_Gδ {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P3 A → ∃ G, IsOpen G ∧ (∀ n : ℕ, ∃ U, IsOpen U ∧ closure U ⊆ G) ∧ closure G = closure A := by
  intro hP3
  rcases exists_dense_open_of_P3 (A := A) hP3 with ⟨G, hG_open, hG_closure⟩
  refine ⟨G, hG_open, ?_, hG_closure⟩
  intro n
  refine ⟨(∅ : Set X), isOpen_empty, ?_⟩
  simp

theorem P2_sdiff_closed {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P2 A) (hB : IsClosed B) : Topology.P2 (A \ B) := by
  intro x hx
  -- Split the membership information.
  have hxA : x ∈ A := hx.1
  have hx_notB : x ∈ (Bᶜ : Set X) := by
    simpa using hx.2
  -- `P2 A` yields this interior membership.
  have hxU : x ∈ interior (closure (interior A)) := hA hxA
  -- Define the auxiliary open neighbourhood
  have hU_open : IsOpen (interior (closure (interior A))) := isOpen_interior
  have hV_open :
      IsOpen (interior (closure (interior A)) ∩ (Bᶜ : Set X)) :=
    hU_open.inter hB.isOpen_compl
  have hxV :
      x ∈ (interior (closure (interior A)) ∩ (Bᶜ : Set X)) := by
    exact And.intro hxU hx_notB
  -- Show that this neighbourhood is contained in the desired closure.
  have hV_subset :
      (interior (closure (interior A)) ∩ (Bᶜ : Set X) : Set X) ⊆
        closure (interior (A \ B)) := by
    intro y hyV
    -- Extract the facts about `y`.
    have hyU : y ∈ interior (closure (interior A)) := hyV.1
    have hy_notB : y ∈ (Bᶜ : Set X) := hyV.2
    -- Hence `y ∈ closure (interior A)`.
    have hy_cl :
        y ∈ closure (interior A) := by
      have h_sub :
          (interior (closure (interior A)) : Set X) ⊆
            closure (interior A) := interior_subset
      exact h_sub hyU
    -- Prove that `y` belongs to `closure (interior (A \ B))`.
    have : y ∈ closure (interior (A \ B)) := by
      -- Use the neighbourhood formulation of the closure.
      apply (mem_closure_iff).2
      intro W hW_open hyW
      -- Remove the portion inside `B`.
      have hW'_open : IsOpen (W ∩ (Bᶜ : Set X)) :=
        hW_open.inter hB.isOpen_compl
      have hyW' : y ∈ W ∩ (Bᶜ : Set X) := And.intro hyW hy_notB
      -- Since `y ∈ closure (interior A)`, obtain a point of
      -- `interior A` in this neighbourhood.
      rcases
          (mem_closure_iff).1 hy_cl _ hW'_open hyW' with
        ⟨z, hzW', hz_intA⟩
      -- Split the obtained information.
      have hzW : z ∈ W := hzW'.1
      have hz_notB : z ∈ (Bᶜ : Set X) := hzW'.2
      -- We claim that `z ∈ interior (A \ B)`.
      have hz_int_diff : z ∈ interior (A \ B) := by
        -- The open set `interior A ∩ Bᶜ` is contained in `A \ B`.
        have h_basic :
            (interior A ∩ (Bᶜ : Set X) : Set X) ⊆ (A \ B) := by
          intro t ht
          exact And.intro (interior_subset ht.1) ht.2
        have h_open :
            IsOpen (interior A ∩ (Bᶜ : Set X) : Set X) :=
          (isOpen_interior.inter hB.isOpen_compl)
        have h_sub :
            (interior A ∩ (Bᶜ : Set X) : Set X) ⊆
              interior (A \ B) :=
          interior_maximal h_basic h_open
        have hz_mem : z ∈ (interior A ∩ (Bᶜ : Set X) : Set X) :=
          And.intro hz_intA hz_notB
        exact h_sub hz_mem
      -- Provide the desired witness.
      exact ⟨z, And.intro hzW hz_int_diff⟩
    exact this
  -- The neighbourhood is open, hence contained in the interior of the closure.
  have hV_subset_int :
      (interior (closure (interior A)) ∩ (Bᶜ : Set X) : Set X) ⊆
        interior (closure (interior (A \ B))) :=
    interior_maximal hV_subset hV_open
  -- Conclude for the original point `x`.
  exact hV_subset_int hxV

theorem P2_prod_univ {X : Type*} [TopologicalSpace X] {A : Set X} {Y : Type*} [TopologicalSpace Y] (h : Topology.P2 A) : Topology.P2 (A ×ˢ (Set.univ : Set Y)) := by
  have hUniv : Topology.P2 (Set.univ : Set Y) := P2_univ
  simpa using (P2_prod (A := A) (B := (Set.univ : Set Y)) h hUniv)

theorem P2_of_closed_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) (h_dense : closure A = Set.univ) : Topology.P2 A := by
  -- A closed dense set must be the whole space.
  have hA_univ : (A : Set X) = Set.univ := by
    simpa [hA_closed.closure_eq] using h_dense
  -- `P2` holds for `Set.univ`; transport this fact to `A`.
  simpa [hA_univ] using (P2_univ : Topology.P2 (Set.univ : Set X))

theorem P1_of_P3_and_closed {X : Type*} [TopologicalSpace X] {A : Set X} (h_closed : IsClosed A) (hP3 : Topology.P3 A) : Topology.P1 A := by
  intro x hxA
  -- Use `P3` to place `x` inside `interior (closure A)`,
  -- then rewrite with the fact that `A` is closed.
  have hx_int : x ∈ interior (A : Set X) := by
    have : x ∈ interior (closure (A : Set X)) := hP3 hxA
    simpa [h_closed.closure_eq] using this
  -- The closure contains its interior.
  exact subset_closure hx_int

theorem P1_prod_prod {X₁ : Type*} [TopologicalSpace X₁] {X₂ : Type*} [TopologicalSpace X₂] {Y₁ : Type*} [TopologicalSpace Y₁] {Y₂ : Type*} [TopologicalSpace Y₂] {A : Set X₁} {B : Set X₂} {C : Set Y₁} {D : Set Y₂} (h1 : Topology.P1 A) (h2 : Topology.P1 B) (h3 : Topology.P1 C) (h4 : Topology.P1 D) : Topology.P1 ((A ×ˢ B) ×ˢ (C ×ˢ D)) := by
  have hAB : Topology.P1 (A ×ˢ B) := P1_prod h1 h2
  have hCD : Topology.P1 (C ×ˢ D) := P1_prod h3 h4
  simpa using P1_prod hAB hCD

theorem P2_prod_univ_rev {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y] {A : Set Y} (hA : Topology.P2 A) : Topology.P2 ((Set.univ : Set X) ×ˢ A) := by
  have hUniv : Topology.P2 (Set.univ : Set X) := P2_univ
  simpa using (P2_prod (A := (Set.univ : Set X)) (B := A) hUniv hA)

theorem P3_prod_univ_rev {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y] {A : Set Y} (hA : Topology.P3 A) : Topology.P3 ((Set.univ : Set X) ×ˢ A) := by
  have hUniv : Topology.P3 (Set.univ : Set X) := P3_univ
  simpa using (P3_prod (A := (Set.univ : Set X)) (B := A) hUniv hA)

theorem exists_open_subset_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P2 A) : ∃ U, IsOpen U ∧ A ⊆ closure U ∧ U ⊆ closure (interior A) := by
  refine ⟨interior (closure (interior A)), isOpen_interior, ?_, ?_⟩
  · intro x hx
    exact subset_closure (hA hx)
  ·
    exact interior_subset

theorem P3_iff_P2_of_nowhere_dense {X : Type*} [TopologicalSpace X] {A : Set X} (h : interior (closure A) = ∅) : Topology.P3 A ↔ Topology.P2 A := by
  constructor
  · intro hP3
    -- First, show that `A` is empty.
    have hAempty : (A : Set X) = ∅ := by
      classical
      apply Set.eq_empty_iff_forall_not_mem.2
      intro x hx
      have : x ∈ interior (closure (A : Set X)) := hP3 hx
      simpa [h] using this
    -- `P2` holds for the empty set, hence for `A`.
    simpa [hAempty] using (P2_empty : Topology.P2 (∅ : Set X))
  · exact P3_of_P2

theorem P1_exists_dense_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P1 A) : ∃ U, IsOpen U ∧ closure U = closure A ∧ Topology.P2 U := by
  refine ⟨interior A, isOpen_interior, ?_, ?_⟩
  · simpa using (P1_iff_closure_interior_eq_closure (A := A)).1 hA
  · simpa using (P2_interior (A := A))

theorem P3_closed_complement {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P3 Aᶜ := by
  exact P3_of_open hA.isOpen_compl

theorem P2_bUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {F : ι → Set X} (h : ∀ i, Topology.P2 (F i)) : Topology.P2 (⋃ i, F i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxFi⟩
  have hxi : x ∈ interior (closure (interior (F i))) := (h i) hxFi
  have hsubset :
      interior (closure (interior (F i))) ⊆
        interior (closure (interior (⋃ i, F i))) := by
    -- `F i ⊆ ⋃ j, F j`
    have h₁ : (F i : Set X) ⊆ ⋃ j, F j := by
      intro y hy
      exact Set.mem_iUnion_of_mem i hy
    -- Apply monotonicity of `interior` and `closure`
    have h₂ : interior (F i) ⊆ interior (⋃ j, F j) := interior_mono h₁
    have h₃ :
        closure (interior (F i)) ⊆ closure (interior (⋃ j, F j)) :=
      closure_mono h₂
    exact interior_mono h₃
  exact hsubset hxi

theorem P2_of_P1_and_eq {X : Type*} [TopologicalSpace X] {A : Set X} (hP1 : Topology.P1 A) (hEq : closure (interior A) = interior (closure A)) : Topology.P2 A := by
  intro x hxA
  -- `P1` gives membership in the closure of the interior.
  have h1 : x ∈ closure (interior A) := hP1 hxA
  -- Rewrite with the given equality to land in `interior (closure A)`.
  have h2 : x ∈ interior (closure A) := by
    simpa [hEq] using h1
  -- Re-express the goal via the same equality (plus `interior_interior`)
  -- and conclude.
  simpa [hEq, interior_interior] using h2

theorem P3_of_closure_eq_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure A = interior (closure A)) : Topology.P3 A := by
  intro x hxA
  have hx_cl : x ∈ closure (A : Set X) := subset_closure hxA
  simpa using (h ▸ hx_cl)

theorem P2_of_discrete {X : Type*} [TopologicalSpace X] [DiscreteTopology X] (A : Set X) : Topology.P2 A := by
  intro x hx
  -- `A` is open in a discrete space, hence `interior A = A`.
  have hA_open : IsOpen (A : Set X) := isOpen_discrete _
  have hx_intA : x ∈ interior A := by
    simpa [hA_open.interior_eq] using hx
  -- We have `A ⊆ closure (interior A)` (which equals `closure A`).
  have h_subset : (A : Set X) ⊆ closure (interior A) := by
    simpa [hA_open.interior_eq] using
      (subset_closure : (A : Set X) ⊆ closure A)
  -- Taking interiors preserves inclusions.
  have h_subset_int :
      interior A ⊆ interior (closure (interior A)) :=
    interior_mono h_subset
  exact h_subset_int hx_intA

theorem P2_complement_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) (hP2 : Topology.P2 A) : Topology.P2 Aᶜ := by
  exact P2_of_open hA.isOpen_compl

theorem P2_iff_double_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A ↔ A ⊆ interior (interior (closure (interior A))) := by
  -- `interior` is idempotent
  have h_eq :
      interior (interior (closure (interior A))) =
        interior (closure (interior A)) := by
    simp [interior_interior]
  constructor
  · intro hP2 x hxA
    have : x ∈ interior (closure (interior A)) := hP2 hxA
    simpa [h_eq] using this
  · intro hSub x hxA
    have : x ∈ interior (interior (closure (interior A))) := hSub hxA
    simpa [h_eq] using this

theorem P1_iff_nhd_closure {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A ↔ (∀ x ∈ A, ∀ U, IsOpen U → x ∈ U → (U ∩ interior A).Nonempty) := by
  classical
  constructor
  · intro hP1 x hxA U hU_open hxU
    have hx_cl : x ∈ closure (interior A) := hP1 hxA
    exact ((mem_closure_iff).1 hx_cl) U hU_open hxU
  · intro h x hxA
    have h' : ∀ U, IsOpen U → x ∈ U → (U ∩ interior A).Nonempty := by
      intro U hU_open hxU
      exact h x hxA U hU_open hxU
    exact (mem_closure_iff).2 h'

theorem P3_sUnion_closed {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} : (∀ A ∈ 𝒜, IsClosed A ∧ Topology.P3 A) → Topology.P3 (⋃₀ 𝒜) := by
  intro h
  have hP3 : ∀ A ∈ 𝒜, Topology.P3 A := by
    intro A hA
    exact (h A hA).2
  exact P3_sUnion (𝒜 := 𝒜) hP3

theorem P1_closed_complement {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P1 Aᶜ := by
  simpa using (open_implies_P1 hA.isOpen_compl)

theorem P1_image_of_continuous_open_map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {f : X → Y} (hf : Continuous f) (hf_open : IsOpenMap f) (hA : Topology.P1 A) : Topology.P1 (f '' A) := by
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  have hx_cl : x ∈ closure (interior (A : Set X)) := hA hxA
  -- First, show `f x ∈ closure (f '' interior A)`.
  have h1 : f x ∈ closure (f '' interior (A : Set X)) := by
    apply (mem_closure_iff).2
    intro V hV_open hxV
    have h_pre_open : IsOpen (f ⁻¹' V) := hV_open.preimage hf
    have hx_pre : x ∈ f ⁻¹' V := by
      simpa using hxV
    rcases
        (mem_closure_iff).1 hx_cl (f ⁻¹' V) h_pre_open hx_pre with
      ⟨z, hz_pre, hz_int⟩
    refine ⟨f z, ?_⟩
    have hzV : f z ∈ V := by
      simpa using hz_pre
    have hz_img : f z ∈ f '' interior (A : Set X) := ⟨z, hz_int, rfl⟩
    exact And.intro hzV hz_img
  -- `f '' interior A` is open and sits inside `f '' A`.
  have h_open : IsOpen (f '' interior (A : Set X)) := by
    simpa using hf_open _ isOpen_interior
  have h_subset_img :
      (f '' interior (A : Set X) : Set Y) ⊆ f '' A := by
    intro z hz
    rcases hz with ⟨u, hu_int, rfl⟩
    exact ⟨u, interior_subset hu_int, rfl⟩
  have h_subset_int :
      (f '' interior (A : Set X) : Set Y) ⊆ interior (f '' A) :=
    interior_maximal h_subset_img h_open
  have h_closure_subset :
      closure (f '' interior (A : Set X)) ⊆ closure (interior (f '' A)) :=
    closure_mono h_subset_int
  exact h_closure_subset h1

theorem P3_closed_iff_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P3 A ↔ IsOpen A := by
  constructor
  · intro hP3
    exact open_of_closed_and_P3 hA hP3
  · intro hOpen
    exact P3_of_open hOpen

theorem P2_iff_P1_of_dense_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h_dense : closure A = Set.univ) : Topology.P2 A ↔ Topology.P1 A := by
  -- Since `closure A = univ`, we have `P3 A`.
  have hP3 : Topology.P3 A := P3_of_dense (A := A) h_dense
  -- `P2 A` is equivalent to `P1 A ∧ P3 A`.
  have h₁ : Topology.P2 A ↔ (Topology.P1 A ∧ Topology.P3 A) :=
    (P1_and_P3_equiv_P2 (A := A)).symm
  -- Because `P3 A` is true, `P1 A ∧ P3 A` is equivalent to `P1 A`.
  have h₂ : (Topology.P1 A ∧ Topology.P3 A) ↔ Topology.P1 A := by
    constructor
    · intro h; exact h.1
    · intro hP1; exact ⟨hP1, hP3⟩
  -- Combine the two equivalences.
  exact h₁.trans h₂

theorem P3_of_open_with_same_closure {X : Type*} [TopologicalSpace X] {A U : Set X} (hUopen : IsOpen U) (hAU : A ⊆ U) (hClos : closure U = closure A) : Topology.P3 A := by
  intro x hxA
  have hxU : x ∈ U := hAU hxA
  have hP3U : P3 U := P3_of_open hUopen
  have hInt : x ∈ interior (closure U) := hP3U hxU
  simpa [hClos] using hInt

theorem exists_open_subset_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hP3 : Topology.P3 A) : ∃ U, IsOpen U ∧ A ⊆ U ∧ U ⊆ interior (closure A) := by
  refine ⟨interior (closure (A : Set X)), isOpen_interior, ?_, subset_refl _⟩
  intro x hxA
  exact hP3 hxA

theorem P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P3 (closure A)) : Topology.P3 A := by
  intro x hxA
  have hx_closure : x ∈ closure (A : Set X) := subset_closure hxA
  have hx_int : x ∈ interior (closure (closure (A : Set X))) := h hx_closure
  simpa [closure_closure] using hx_int

theorem exists_open_dense_subset_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hP3 : Topology.P3 A) : ∃ U, IsOpen U ∧ closure U = closure A ∧ interior (closure A) ⊆ U := by
  refine ⟨interior (closure (A : Set X)), isOpen_interior, ?_, ?_⟩
  · -- Show `closure U = closure A`
    apply subset_antisymm
    · -- `closure U ⊆ closure A`
      have :
          closure (interior (closure (A : Set X))) ⊆
            closure (closure (A : Set X)) :=
        closure_mono
          (interior_subset :
            interior (closure (A : Set X)) ⊆ closure (A : Set X))
      simpa [closure_closure] using this
    · -- `closure A ⊆ closure U` thanks to `P3`
      have h : (A : Set X) ⊆ interior (closure (A : Set X)) := hP3
      exact closure_mono h
  · -- Trivial inclusion `interior (closure A) ⊆ U`
    exact subset_rfl

theorem P3_sUnion_open {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (h𝒜 : ∀ A ∈ 𝒜, IsOpen A) : Topology.P3 (⋃₀ 𝒜) := by
  refine P3_sUnion (𝒜 := 𝒜) ?_
  intro A hA
  exact P3_of_open (h𝒜 A hA)

theorem P2_closed_complement' {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → Topology.P2 Aᶜ := by
  intro hClosed
  exact P2_of_open hClosed.isOpen_compl

theorem P2_prod_symm {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y] {A : Set X} {B : Set Y} : Topology.P2 (A ×ˢ B) → Topology.P2 (B ×ˢ A) := by
  intro hP2
  ----------------------------------------------------------------
  -- 1.  The homeomorphism swapping the two coordinates.
  ----------------------------------------------------------------
  let hComm : (X × Y) ≃ₜ (Y × X) := Homeomorph.prodComm X Y
  ----------------------------------------------------------------
  -- 2.  Transport `P2` through this homeomorphism.
  ----------------------------------------------------------------
  have hP2_image :
      Topology.P2 ((hComm) '' (A ×ˢ B : Set (X × Y))) :=
    P2_image_of_homeomorph (A := A ×ˢ B) (h := hComm) hP2
  ----------------------------------------------------------------
  -- 3.  Identify the image `hComm '' (A ×ˢ B)` with `B ×ˢ A`.
  ----------------------------------------------------------------
  have hImage :
      ((hComm) '' (A ×ˢ B : Set (X × Y)) : Set (Y × X)) = B ×ˢ A := by
    ext p
    constructor
    · -- `p` comes from the image
      rintro ⟨q, hqAB, rfl⟩
      rcases q with ⟨x, y⟩
      rcases hqAB with ⟨hxA, hyB⟩
      -- After swapping we get `(y, x)`
      -- Show this belongs to `B ×ˢ A`
      simpa [hComm, Homeomorph.prodComm, Set.mem_prod] using
        And.intro hyB hxA
    · -- Start with a point in `B ×ˢ A`
      intro hp
      rcases p with ⟨y, x⟩
      have hp' : y ∈ B ∧ x ∈ A := by
        simpa [Set.mem_prod] using hp
      -- Pre-image point `(x, y)` lies in `A ×ˢ B`
      have hqAB : (x, y) ∈ (A ×ˢ B : Set (X × Y)) := by
        simpa [Set.mem_prod] using And.intro hp'.2 hp'.1
      -- Its image under `hComm` is `(y, x)`
      have : (y, x) ∈ ((hComm) '' (A ×ˢ B : Set (X × Y))) := by
        refine ⟨(x, y), hqAB, ?_⟩
        simp [hComm, Homeomorph.prodComm]
      simpa using this
  ----------------------------------------------------------------
  -- 4.  Rewrite with the computed image and conclude.
  ----------------------------------------------------------------
  simpa [hImage] using hP2_image

theorem P1_restrict {X : Type*} [TopologicalSpace X] {A : Set X} {U : Set X} (hU : IsOpen U) : Topology.P1 A → Topology.P1 (A ∩ U) := by
  intro hP1
  intro x hx
  rcases hx with ⟨hxA, hxU⟩
  -- `x` is in the closure of `interior A`
  have hx_cl : x ∈ closure (interior (A : Set X)) := hP1 hxA
  -- Use the neighbourhood criterion for closures
  apply (mem_closure_iff).2
  intro V hV_open hxV
  -- Work inside the open set `V ∩ U`
  have hW_open : IsOpen (V ∩ U) := hV_open.inter hU
  have hxW : x ∈ V ∩ U := And.intro hxV hxU
  -- `V ∩ U` meets `interior A`
  rcases (mem_closure_iff).1 hx_cl (V ∩ U) hW_open hxW with
    ⟨y, hyW, hy_intA⟩
  -- From `y ∈ interior A ∩ U`, deduce `y ∈ interior (A ∩ U)`
  have hy_intAU : y ∈ interior (A ∩ U) := by
    -- `interior A ∩ U` is an open subset of `A ∩ U`
    have h_subset :
        (interior (A : Set X) ∩ U : Set X) ⊆ interior (A ∩ U) := by
      have h_open : IsOpen (interior (A : Set X) ∩ U) :=
        isOpen_interior.inter hU
      have h_basic :
          (interior (A : Set X) ∩ U : Set X) ⊆ A ∩ U := by
        intro z hz
        exact And.intro (interior_subset hz.1) hz.2
      exact interior_maximal h_basic h_open
    have : y ∈ interior (A : Set X) ∩ U := And.intro hy_intA hyW.2
    exact h_subset this
  -- Provide the required witness in `V ∩ interior (A ∩ U)`
  exact ⟨y, And.intro hyW.1 hy_intAU⟩

theorem P1_prod_three {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y] {Z : Type*} [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : Topology.P1 A → Topology.P1 B → Topology.P1 C → Topology.P1 (A ×ˢ B ×ˢ C) := by
  intro hA hB hC
  -- First, obtain `P1` for the product `B ×ˢ C`.
  have hBC : Topology.P1 (B ×ˢ C) := P1_prod hB hC
  -- Next, combine this with `A` to get the desired triple product.
  have hABC : Topology.P1 (A ×ˢ (B ×ˢ C)) := P1_prod hA hBC
  simpa using hABC

theorem P2_homeomorph_symm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set Y} (h : Homeomorph X Y) : Topology.P2 (h.symm '' A) → Topology.P2 A := by
  intro hP2_symm
  -- Transport `P2` through the homeomorphism `h`
  have hP2_image : Topology.P2 (h '' (h.symm '' A) : Set Y) :=
    P2_image_of_homeomorph (A := h.symm '' A) (h := h) hP2_symm
  -- Identify the image with `A`
  have hImage : (h '' (h.symm '' A) : Set Y) = A := by
    ext y
    constructor
    · rintro ⟨x, ⟨z, hzA, rfl⟩, rfl⟩
      simpa using hzA
    · intro hyA
      refine ⟨h.symm y, ?_, ?_⟩
      · exact ⟨y, hyA, by
          simp⟩
      · simpa using h.apply_symm_apply y
  -- Conclude using the computed equality
  simpa [hImage] using hP2_image