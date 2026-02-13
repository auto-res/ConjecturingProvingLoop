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


theorem P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A := by
  intro x hx
  -- `A` is open, so its interior is itself
  have hInt : interior A = A := hA.interior_eq
  -- hence `x ∈ interior A`
  have hx_int : x ∈ interior A := by
    simpa [hInt] using hx
  -- `interior A` is an open subset of `closure (interior A)`,
  -- so it is contained in the interior of this closure
  have h_subset : interior A ⊆ interior (closure (interior A)) := by
    apply interior_maximal
    · exact subset_closure
    · exact isOpen_interior
  exact h_subset hx_int

theorem P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P3 A := by
  intro x hx
  have hP2 : P2 A := P2_of_open hA
  have hInt : interior A = A := hA.interior_eq
  have : x ∈ interior (closure (interior A)) := hP2 hx
  simpa [hInt] using this

theorem P2_subset_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P1 A := by
  intro hP2
  exact fun x hx => interior_subset (hP2 hx)

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P1 A → P1 B → P1 (A ∪ B) := by
  intro hP1A hP1B
  intro x hx
  cases hx with
  | inl hxA =>
      have hx_closure : x ∈ closure (interior A) := hP1A hxA
      have hsubset : interior A ⊆ interior (A ∪ B) :=
        interior_mono (by
          intro y hy
          exact Or.inl hy)
      exact (closure_mono hsubset) hx_closure
  | inr hxB =>
      have hx_closure : x ∈ closure (interior B) := hP1B hxB
      have hsubset : interior B ⊆ interior (A ∪ B) :=
        interior_mono (by
          intro y hy
          exact Or.inr hy)
      exact (closure_mono hsubset) hx_closure

theorem P1_idempotent {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (closure (interior A)) := by
  intro x hx
  -- `interior A` is contained in `closure (interior A)` and is open,
  -- hence it is contained in the interior of that closure
  have hsubset : interior A ⊆ interior (closure (interior A)) := by
    apply interior_maximal
    · exact subset_closure
    · exact isOpen_interior
  -- Taking closures preserves inclusions
  have hclosure :
      closure (interior A) ⊆ closure (interior (closure (interior A))) :=
    closure_mono hsubset
  exact hclosure hx

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : closure A = Set.univ) : P3 A := by
  intro x hx
  -- The interior of the closure is the whole space, since the closure is the whole space.
  have h_int : interior (closure A) = (Set.univ : Set X) := by
    simpa [hA, interior_univ]
  -- Every point is in the whole space.
  have hx_univ : x ∈ (Set.univ : Set X) := by
    simp
  -- Hence the desired inclusion holds.
  simpa [h_int] using hx_univ

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P2 A → P2 B → P2 (A ∪ B) := by
  intro hP2A hP2B
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x` comes from `A`
      have hx_in : x ∈ interior (closure (interior A)) := hP2A hxA
      -- `interior A` is contained in `interior (A ∪ B)`
      have hsubset_int : interior A ⊆ interior (A ∪ B) := by
        apply interior_mono
        intro y hy
        exact Or.inl hy
      -- Taking closures preserves inclusions
      have hsubset_closure :
          closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hsubset_int
      -- Taking interiors preserves inclusions as well
      have hsubset :
          interior (closure (interior A)) ⊆
            interior (closure (interior (A ∪ B))) :=
        interior_mono hsubset_closure
      exact hsubset hx_in
  | inr hxB =>
      -- `x` comes from `B`
      have hx_in : x ∈ interior (closure (interior B)) := hP2B hxB
      -- `interior B` is contained in `interior (A ∪ B)`
      have hsubset_int : interior B ⊆ interior (A ∪ B) := by
        apply interior_mono
        intro y hy
        exact Or.inr hy
      -- Taking closures preserves inclusions
      have hsubset_closure :
          closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hsubset_int
      -- Taking interiors preserves inclusions as well
      have hsubset :
          interior (closure (interior B)) ⊆
            interior (closure (interior (A ∪ B))) :=
        interior_mono hsubset_closure
      exact hsubset hx_in

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P3 A → P3 B → P3 (A ∪ B) := by
  intro hP3A hP3B
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x` comes from `A`
      have hx_int : x ∈ interior (closure A) := hP3A hxA
      -- `closure A` is contained in `closure (A ∪ B)`
      have hsubset_closure : closure A ⊆ closure (A ∪ B) := by
        apply closure_mono
        intro y hy
        exact Or.inl hy
      -- hence their interiors are related
      have hsubset : interior (closure A) ⊆ interior (closure (A ∪ B)) :=
        interior_mono hsubset_closure
      exact hsubset hx_int
  | inr hxB =>
      -- `x` comes from `B`
      have hx_int : x ∈ interior (closure B) := hP3B hxB
      -- `closure B` is contained in `closure (A ∪ B)`
      have hsubset_closure : closure B ⊆ closure (A ∪ B) := by
        apply closure_mono
        intro y hy
        exact Or.inr hy
      -- hence their interiors are related
      have hsubset : interior (closure B) ⊆ interior (closure (A ∪ B)) :=
        interior_mono hsubset_closure
      exact hsubset hx_int

theorem P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P2 (interior A) := by
  intro hP2
  intro x hx
  have hxA : x ∈ (A) := (interior_subset : interior A ⊆ A) hx
  have hmem : x ∈ interior (closure (interior A)) := hP2 hxA
  simpa [interior_interior] using hmem

theorem P3_idempotent {X : Type*} [TopologicalSpace X] {A : Set X} : P3 (interior (closure A)) := by
  intro x hx
  have hsubset :
      interior (closure A) ⊆
        interior (closure (interior (closure A))) := by
    apply interior_maximal
    · exact subset_closure
    · exact isOpen_interior
  exact hsubset hx

theorem P3_union₃ {X : Type*} [TopologicalSpace X] {A B C : Set X} : P3 A → P3 B → P3 C → P3 (A ∪ B ∪ C) := by
  intro hP3A hP3B hP3C
  have hP3_AB : P3 (A ∪ B) := P3_union hP3A hP3B
  have hP3_ABC : P3 ((A ∪ B) ∪ C) := P3_union hP3_AB hP3C
  simpa [Set.union_assoc] using hP3_ABC

theorem P2_iff_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A ↔ P3 A := by
  have hInt : interior A = A := hA.interior_eq
  constructor
  · intro hP2
    intro x hx
    simpa [hInt] using hP2 hx
  · intro hP3
    intro x hx
    simpa [hInt] using hP3 hx

theorem P3_empty {X : Type*} [TopologicalSpace X] : P3 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P2_idempotent {X : Type*} [TopologicalSpace X] {A : Set X} : P2 (interior (closure (interior A))) := by
  intro x hx
  -- First, note that the desired set enjoys the `P3` property
  have hP3 : P3 (interior (closure (interior A))) := by
    simpa using (P3_idempotent (A := interior A))
  -- Apply this inclusion to the given point
  have hmem : x ∈ interior (closure (interior (closure (interior A)))) := hP3 hx
  -- Re-express the goal using `interior_interior`
  simpa [interior_interior] using hmem

theorem P1_implies_dense {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → closure (interior A) = closure A := by
  intro hP1
  apply Set.Subset.antisymm
  ·
    exact closure_mono (interior_subset : interior A ⊆ A)
  ·
    have h : closure A ⊆ closure (closure (interior A)) := closure_mono hP1
    simpa [closure_closure] using h

theorem P1_iff_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ closure (interior A) = closure A := by
  constructor
  · intro hP1
    exact P1_implies_dense (A := A) hP1
  · intro h_eq
    intro x hx
    have hmem : x ∈ closure A := subset_closure hx
    simpa [h_eq] using hmem

theorem P2_subset_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P3 A := by
  intro hP2
  intro x hx
  have hx₁ : x ∈ interior (closure (interior A)) := hP2 hx
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono (closure_mono (interior_subset : interior A ⊆ A))
  exact hsubset hx₁

theorem P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → P1 (interior A) := by
  intro _hP1
  intro x hx
  simpa [interior_interior] using (subset_closure hx)

theorem P2_iff_P3_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P2 A ↔ P3 A := by
  constructor
  ·
    exact P2_subset_P3 (A := A)
  ·
    intro hP3
    -- Show `A ⊆ interior A`
    have hsubset : (A : Set X) ⊆ interior A := by
      intro x hx
      have : x ∈ interior (closure A) := hP3 hx
      simpa [hA.closure_eq] using this
    -- Hence `interior A = A`
    have hInt_eq : interior A = A := by
      apply Set.Subset.antisymm
      · exact interior_subset
      · exact hsubset
    -- Therefore `A` is open
    have hA_open : IsOpen A := by
      have : IsOpen (interior A) := isOpen_interior
      simpa [hInt_eq] using this
    -- Apply the open-set version of `P2`
    exact P2_of_open hA_open

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} : (∀ A, A ∈ 𝒜 → P1 A) → P1 (⋃₀ 𝒜) := by
  intro hAll
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP1A : P1 A := hAll A hA_mem
  have hx_closure : x ∈ closure (interior A) := hP1A hxA
  have hA_subset_union : (A : Set X) ⊆ ⋃₀ 𝒜 := by
    intro z hz
    exact Set.mem_sUnion.2 ⟨A, hA_mem, hz⟩
  have hsubset_interior : interior A ⊆ interior (⋃₀ 𝒜) :=
    interior_mono hA_subset_union
  have hsubset_closure :
      closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) :=
    closure_mono hsubset_interior
  exact hsubset_closure hx_closure

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} : (∀ A, A ∈ 𝒜 → P2 A) → P2 (⋃₀ 𝒜) := by
  intro hAll
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP2A : P2 A := hAll A hA_mem
  have hx_int : x ∈ interior (closure (interior A)) := hP2A hxA
  have hsubset_interior : interior A ⊆ interior (⋃₀ 𝒜) := by
    apply interior_mono
    intro z hz
    exact Set.mem_sUnion.2 ⟨A, hA_mem, hz⟩
  have hsubset_closure :
      closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) :=
    closure_mono hsubset_interior
  have hsubset :
      interior (closure (interior A)) ⊆
        interior (closure (interior (⋃₀ 𝒜))) :=
    interior_mono hsubset_closure
  exact hsubset hx_int

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} : (∀ A, A ∈ 𝒜 → P3 A) → P3 (⋃₀ 𝒜) := by
  intro hAll
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP3A : P3 A := hAll A hA_mem
  have hx_int : x ∈ interior (closure A) := hP3A hxA
  have hsubset_closure : closure A ⊆ closure (⋃₀ 𝒜) := by
    apply closure_mono
    intro y hy
    exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
  have hsubset : interior (closure A) ⊆ interior (closure (⋃₀ 𝒜)) :=
    interior_mono hsubset_closure
  exact hsubset hx_int

theorem P3_univ {X : Type*} [TopologicalSpace X] : P3 (Set.univ : Set X) := by
  intro x hx
  simpa [closure_univ, interior_univ] using hx

theorem P2_empty {X : Type*} [TopologicalSpace X] : P2 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P1_empty {X : Type*} [TopologicalSpace X] : P1 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P2_univ {X : Type*} [TopologicalSpace X] : P2 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P1_iff_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P1 A ↔ P3 A := by
  have hP2_P3 := (P2_iff_P3_of_open (X := X) (A := A) hA)
  constructor
  · intro _hP1
    exact P3_of_open (X := X) (A := A) hA
  · intro hP3
    have hP2 : P2 A := (hP2_P3).2 hP3
    exact P2_subset_P1 (A := A) hP2

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P3 A → P3 (interior A) := by
  intro _hP3
  intro x hx
  have hsubset : interior A ⊆ interior (closure (interior A)) := by
    apply interior_maximal
    · exact subset_closure
    · exact isOpen_interior
  exact hsubset hx

theorem P1_univ {X : Type*} [TopologicalSpace X] : P1 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} : interior A = (Set.univ : Set X) → P2 A := by
  intro hInt_eq
  intro x hx
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [hInt_eq, closure_univ, interior_univ] using this

theorem P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} : interior A = (Set.univ : Set X) → P3 A := by
  intro hInt_eq
  intro x hx
  -- Since `interior A = univ`, every point lies in `interior A`.
  have hx_intA : x ∈ interior A := by
    simpa [hInt_eq] using (by
      simp : x ∈ (Set.univ : Set X))
  -- `interior A` is contained in `interior (closure A)`.
  have hsubset : interior A ⊆ interior (closure A) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  exact hsubset hx_intA

theorem P2_compl_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P2 (Aᶜ) := by
  -- The complement of a closed set is open.
  have hOpen : IsOpen (Aᶜ) := (isOpen_compl_iff).2 hA
  -- Apply the lemma for open sets.
  exact P2_of_open (X := X) (A := Aᶜ) hOpen

theorem P3_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (e : X ≃ₜ Y) : P3 A → P3 (e '' A) := by
  intro hP3
  intro y hy
  -- pick a preimage of `y`
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` is in the interior of the closure of `A`
  have hx_int : x ∈ interior (closure A) := hP3 hxA
  ------------------------------------------------------------------
  -- Define the open neighbourhood on `Y`
  ------------------------------------------------------------------
  set U : Set Y := e.symm ⁻¹' interior (closure A) with hU_def
  have hU_open : IsOpen U := by
    simpa [hU_def] using (isOpen_interior).preimage e.symm.continuous
  -- `e x` lies in `U`
  have hxU : (e x) ∈ U := by
    change e.symm (e x) ∈ interior (closure A) at *
    simpa [e.symm_apply_apply] using hx_int
  ------------------------------------------------------------------
  -- Show `U ⊆ closure (e '' A)`
  ------------------------------------------------------------------
  have hU_subset : U ⊆ closure (e '' A) := by
    intro z hzU
    -- Let `u` be the preimage of `z`
    have hu_int : e.symm z ∈ interior (closure A) := by
      simpa [hU_def] using hzU
    have hu_cl : e.symm z ∈ closure A :=
      interior_subset hu_int
    -- Show `z ∈ closure (e '' A)`
    have hz_closure : z ∈ closure (e '' A) := by
      -- use the neighbourhood characterisation of the closure
      apply (mem_closure_iff).2
      intro V hVopen hzV
      -- Preimage of `V` under `e`
      have hWopen : IsOpen (e ⁻¹' V) :=
        hVopen.preimage e.continuous
      have huW : e.symm z ∈ e ⁻¹' V := by
        change e (e.symm z) ∈ V
        simpa using hzV
      -- Intersect with `A`
      have h_nonempty :
          ((e ⁻¹' V) ∩ A).Nonempty :=
        (mem_closure_iff).1 hu_cl (e ⁻¹' V) hWopen huW
      rcases h_nonempty with ⟨w, hwW, hwA⟩
      -- Map this point with `e`
      have hwV : e w ∈ V := by
        -- `w ∈ e ⁻¹' V` gives `e w ∈ V`
        simpa [Set.mem_preimage] using hwW
      have hw_img : e w ∈ e '' A := ⟨w, hwA, rfl⟩
      exact ⟨e w, hwV, hw_img⟩
    exact hz_closure
  ------------------------------------------------------------------
  -- Conclude: `e x` is in the interior of the closure
  ------------------------------------------------------------------
  have hU_interior :
      U ⊆ interior (closure (e '' A)) := by
    apply interior_maximal
    · exact hU_subset
    · exact hU_open
  exact hU_interior hxU

theorem P2_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (e : X ≃ₜ Y) : P2 A → P2 (e '' A) := by
  intro hP2
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` enjoys the `P2` property
  have hx_int : x ∈ interior (closure (interior A)) := hP2 hxA
  ------------------------------------------------------------------
  -- An open neighbourhood of `e x`
  ------------------------------------------------------------------
  set U : Set Y := e.symm ⁻¹' interior (closure (interior A)) with hU_def
  have hU_open : IsOpen U := by
    simpa [hU_def] using
      (isOpen_interior).preimage e.symm.continuous
  have hxU : (e x) ∈ U := by
    have : e.symm (e x) ∈ interior (closure (interior A)) := by
      simpa [e.symm_apply_apply] using hx_int
    simpa [hU_def] using this
  ------------------------------------------------------------------
  -- Show that `U ⊆ closure (interior (e '' A))`
  ------------------------------------------------------------------
  have hU_subset : U ⊆ closure (interior (e '' A)) := by
    intro z hzU
    have hz_int : e.symm z ∈ interior (closure (interior A)) := by
      simpa [hU_def] using hzU
    have hz_cl : e.symm z ∈ closure (interior A) :=
      interior_subset hz_int
    -- Use the neighbourhood characterisation of the closure
    have hz_closure : z ∈ closure (interior (e '' A)) := by
      apply (mem_closure_iff).2
      intro V hVopen hzV
      -- Preimage of `V`
      have hWopen : IsOpen (e ⁻¹' V) :=
        hVopen.preimage e.continuous
      have hzW : e.symm z ∈ e ⁻¹' V := by
        change e (e.symm z) ∈ V
        simpa using hzV
      -- Intersect with `interior A`
      have h_nonempty :
          ((e ⁻¹' V) ∩ interior A).Nonempty :=
        (mem_closure_iff).1 hz_cl (e ⁻¹' V) hWopen hzW
      rcases h_nonempty with ⟨w, hwW, hw_intA⟩
      ----------------------------------------------------------------
      -- `e w` will lie in `V ∩ interior (e '' A)`
      ----------------------------------------------------------------
      have hwV : e w ∈ V := by
        have : w ∈ e ⁻¹' V := hwW
        simpa [Set.mem_preimage] using this
      -- Build an open set in `e '' A` that contains `e w`
      let S : Set Y := (e.symm) ⁻¹' interior A
      have hS_open : IsOpen S :=
        (isOpen_interior).preimage e.symm.continuous
      have hS_sub : (S : Set Y) ⊆ e '' A := by
        intro y hyS
        have hy_int : e.symm y ∈ interior A := hyS
        have hyA : e.symm y ∈ A := interior_subset hy_int
        exact ⟨e.symm y, hyA, by simp⟩
      have hS_to_int : (S : Set Y) ⊆ interior (e '' A) := by
        apply interior_maximal
        · exact hS_sub
        · exact hS_open
      have h_e_w_S : e w ∈ S := by
        change e.symm (e w) ∈ interior A
        simpa [e.symm_apply_apply] using hw_intA
      have hw_intEA : e w ∈ interior (e '' A) :=
        hS_to_int h_e_w_S
      exact ⟨e w, hwV, hw_intEA⟩
    exact hz_closure
  ------------------------------------------------------------------
  -- `U` is an open subset of `closure (interior (e '' A))`
  ------------------------------------------------------------------
  have hU_interior :
      U ⊆ interior (closure (interior (e '' A))) := by
    apply interior_maximal
    · exact hU_subset
    · exact hU_open
  exact hU_interior hxU

theorem P1_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (e : X ≃ₜ Y) : P1 A → P1 (e '' A) := by
  intro hP1
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- use the `P1` property for `x`
  have hx_cl : x ∈ closure (interior A) := hP1 hxA
  -- show `e x` lies in the closure of `e '' interior A`
  have hx_closure : (e x) ∈ closure (e '' interior A) := by
    apply (mem_closure_iff).2
    intro V hVopen hVmem
    -- consider the preimage of `V` under `e`
    have hWopen : IsOpen (e ⁻¹' V) := hVopen.preimage e.continuous
    have hxW : x ∈ e ⁻¹' V := by
      change e x ∈ V at hVmem
      simpa using hVmem
    -- use that `x` is in the closure of `interior A`
    have h_nonempty :=
      (mem_closure_iff).1 hx_cl (e ⁻¹' V) hWopen hxW
    rcases h_nonempty with ⟨w, hwW, hwIntA⟩
    -- map the witness with `e`
    have hwV : e w ∈ V := by
      have : w ∈ e ⁻¹' V := hwW
      simpa [Set.mem_preimage] using this
    have hw_img : e w ∈ e '' interior A := ⟨w, hwIntA, rfl⟩
    exact ⟨e w, hwV, hw_img⟩
  -- `e '' interior A` is an open subset of `e '' A`, hence contained in its interior
  have h_subset_int : (e '' interior A) ⊆ interior (e '' A) := by
    apply interior_maximal
    · intro z hz
      rcases hz with ⟨w, hwIntA, rfl⟩
      exact ⟨w, interior_subset hwIntA, rfl⟩
    ·
      -- prove `e '' interior A` is open
      have hOpen : IsOpen (e '' interior A) := by
        -- express it as the preimage of an open set under `e.symm`
        have h_eq : (e '' interior A) = e.symm ⁻¹' interior A := by
          ext z
          constructor
          · intro hz
            rcases hz with ⟨w, hwIntA, rfl⟩
            change e.symm (e w) ∈ interior A
            simpa [e.symm_apply_apply] using hwIntA
          · intro hz
            have : e.symm z ∈ interior A := hz
            exact ⟨e.symm z, this, by simp⟩
        have hOpen_pre : IsOpen (e.symm ⁻¹' interior A) :=
          (isOpen_interior).preimage e.symm.continuous
        simpa [h_eq] using hOpen_pre
      exact hOpen
  -- taking closures preserves inclusions
  have h_closure_sub :
      closure (e '' interior A) ⊆ closure (interior (e '' A)) :=
    closure_mono h_subset_int
  exact h_closure_sub hx_closure

theorem P1_iff_P2_of_open_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) (h_dense : closure A = Set.univ) : P1 A ↔ P2 A := by
  -- Use the density hypothesis just to avoid an unused-argument warning.
  have _ := h_dense
  -- For open sets we already know `P1 A ↔ P3 A` and `P2 A ↔ P3 A`.
  have hP1_P3 : P1 A ↔ P3 A := P1_iff_P3_of_open (X := X) (A := A) hA
  have hP2_P3 : P2 A ↔ P3 A := P2_iff_P3_of_open (X := X) (A := A) hA
  -- Transitivity of `↔` gives the desired equivalence.
  simpa using hP1_P3.trans hP2_P3.symm

theorem P2_subset_P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P2 A → P1 B → P1 (A ∪ B) := by
  intro hP2 hP1
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x ∈ A`
      have hx_int : x ∈ interior (closure (interior A)) := hP2 hxA
      -- `interior (closure (interior A)) ⊆ closure (interior A)`
      have h1 : interior (closure (interior A)) ⊆ closure (interior A) :=
        interior_subset
      -- `closure (interior A) ⊆ closure (interior (A ∪ B))`
      have h2 : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono (interior_mono (by
          intro y hy
          exact Or.inl hy))
      -- hence the required inclusion
      have hsubset : interior (closure (interior A)) ⊆
          closure (interior (A ∪ B)) := Set.Subset.trans h1 h2
      exact hsubset hx_int
  | inr hxB =>
      -- `x ∈ B`
      have hx_cl : x ∈ closure (interior B) := hP1 hxB
      -- `closure (interior B) ⊆ closure (interior (A ∪ B))`
      have hsubset : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono (interior_mono (by
          intro y hy
          exact Or.inr hy))
      exact hsubset hx_cl

theorem P1_fixedpoint_of_closure {X : Type*} [TopologicalSpace X] {A : Set X} : closure (interior A) = A → P1 A := by
  intro h_eq
  intro x hx
  simpa [h_eq] using hx

theorem P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → P1 (closure A) := by
  intro hP1
  intro x hx
  -- `closure A ⊆ closure (interior A)`
  have h₁ : closure (A : Set X) ⊆ closure (interior A) := by
    simpa [closure_closure] using closure_mono hP1
  -- `closure (interior A) ⊆ closure (interior (closure A))`
  have h₂ :
      closure (interior A) ⊆ closure (interior (closure (A : Set X))) := by
    have hsubset : interior A ⊆ interior (closure (A : Set X)) := by
      apply interior_mono
      exact subset_closure
    exact closure_mono hsubset
  exact h₂ (h₁ hx)

theorem P1_Union_family {X : Type*} [TopologicalSpace X] {ι : Sort _} {F : ι → Set X} (h : ∀ i, P1 (F i)) : P1 (⋃ i, F i) := by
  -- First, show every set in `Set.range F` satisfies `P1`.
  have hAll : ∀ A : Set X, A ∈ Set.range F → P1 A := by
    intro A hA
    rcases hA with ⟨i, rfl⟩
    exact h i
  -- Apply the `sUnion` lemma.
  have hP1_range : P1 (⋃₀ Set.range F) :=
    P1_sUnion (X := X) (𝒜 := Set.range F) hAll
  -- Identify `⋃₀ Set.range F` with `⋃ i, F i`.
  have h_eq : (⋃₀ Set.range F : Set X) = ⋃ i, F i := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
      rcases hA_mem with ⟨i, rfl⟩
      exact Set.mem_iUnion.2 ⟨i, hxA⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hxFi⟩
      exact Set.mem_sUnion.2 ⟨F i, ⟨i, rfl⟩, hxFi⟩
  simpa [h_eq] using hP1_range

theorem P3_iSup_family {X : Type*} [TopologicalSpace X] {ι : Sort _} {F : ι → Set X} (h : ∀ i, P3 (F i)) : P3 (⋃ i, F i) := by
  -- First, show every set in `Set.range F` satisfies `P3`.
  have hAll : ∀ A : Set X, A ∈ Set.range F → P3 A := by
    intro A hA
    rcases hA with ⟨i, rfl⟩
    exact h i
  -- Apply the `sUnion` lemma.
  have hP3_range : P3 (⋃₀ Set.range F) :=
    P3_sUnion (X := X) (𝒜 := Set.range F) hAll
  -- Identify `⋃₀ Set.range F` with `⋃ i, F i`.
  have h_eq : (⋃₀ Set.range F : Set X) = ⋃ i, F i := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
      rcases hA_mem with ⟨i, rfl⟩
      exact Set.mem_iUnion.2 ⟨i, hxA⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hxFi⟩
      exact Set.mem_sUnion.2 ⟨F i, ⟨i, rfl⟩, hxFi⟩
  simpa [h_eq] using hP3_range

theorem P2_of_P3_and_open {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → P3 A → P2 A := by
  intro hA hP3
  exact ((P2_iff_P3_of_open (X := X) (A := A) hA).2) hP3

theorem P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : interior A = Set.univ) : P1 A := by
  intro x hx
  simpa [h, closure_univ] using (Set.mem_univ x)

theorem P1_compl_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → P1 (Aᶜ) := by
  intro hA_closed
  -- The complement of a closed set is open.
  have hOpen : IsOpen (Aᶜ : Set X) := (isOpen_compl_iff).2 hA_closed
  -- Hence its interior is itself.
  have hInt : interior (Aᶜ : Set X) = (Aᶜ : Set X) := hOpen.interior_eq
  -- Now prove the required inclusion.
  intro x hx
  -- Any point of `Aᶜ` is in its closure.
  have hx_closure : x ∈ closure (Aᶜ : Set X) := subset_closure hx
  -- Re-express using `hInt`.
  simpa [hInt] using hx_closure

theorem P2_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P2 A → P2 B → P2 (Set.prod A B) := by
  intro hP2A hP2B
  intro p hp
  -- Split the point into its two coordinates.
  rcases hp with ⟨hpA, hpB⟩
  -- Each coordinate satisfies the `P2` condition.
  have hA : p.1 ∈ interior (closure (interior A)) := hP2A hpA
  have hB : p.2 ∈ interior (closure (interior B)) := hP2B hpB
  ------------------------------------------------------------------
  -- An explicit open neighbourhood of `p`.
  ------------------------------------------------------------------
  set U : Set X := interior (closure (interior A)) with hU
  set V : Set Y := interior (closure (interior B)) with hV
  have hU_open  : IsOpen U := by
    simpa [hU] using isOpen_interior
  have hV_open  : IsOpen V := by
    simpa [hV] using isOpen_interior
  have hUV_open : IsOpen (U ×ˢ V) := hU_open.prod hV_open
  have hpUV : p ∈ U ×ˢ V := by
    have hpU : p.1 ∈ U := by
      simpa [hU] using hA
    have hpV : p.2 ∈ V := by
      simpa [hV] using hB
    exact ⟨hpU, hpV⟩
  ------------------------------------------------------------------
  -- `U ×ˢ V` is contained in the closure of `interior (A ×ˢ B)`.
  ------------------------------------------------------------------
  have h_sub :
      (U ×ˢ V) ⊆ closure (interior (Set.prod A B)) := by
    intro q hq
    rcases hq with ⟨hqU, hqV⟩
    -- Rewrite the memberships.
    have hq1 : q.1 ∈ interior (closure (interior A)) := by
      simpa [hU] using hqU
    have hq2 : q.2 ∈ interior (closure (interior B)) := by
      simpa [hV] using hqV
    -- Pass to the closures of the interiors of the factors.
    have hq1_cl : q.1 ∈ closure (interior A) := interior_subset hq1
    have hq2_cl : q.2 ∈ closure (interior B) := interior_subset hq2
    -- Hence `q` lies in the product of these two closures.
    have hq_prod : q ∈
        (closure (interior A)) ×ˢ (closure (interior B)) :=
      ⟨hq1_cl, hq2_cl⟩
    -- Identify this product with the closure of the product
    -- of the two interiors.
    have h_cl_eq :
        closure ((interior A) ×ˢ (interior B)) =
          (closure (interior A)) ×ˢ (closure (interior B)) := by
      simpa using closure_prod_eq
    have hq_in_cl_prod :
        q ∈ closure ((interior A) ×ˢ (interior B)) := by
      simpa [h_cl_eq] using hq_prod
    -- The product of interiors is contained in the interior
    -- of the product.
    have h_small :
        ((interior A) ×ˢ (interior B)) ⊆ interior (Set.prod A B) := by
      apply interior_maximal
      · intro z hz
        rcases hz with ⟨hz1, hz2⟩
        exact ⟨interior_subset hz1, interior_subset hz2⟩
      · exact (isOpen_interior.prod isOpen_interior)
    -- Taking closures preserves inclusions.
    have h_cl_small :
        closure ((interior A) ×ˢ (interior B)) ⊆
          closure (interior (Set.prod A B)) :=
      closure_mono h_small
    exact h_cl_small hq_in_cl_prod
  ------------------------------------------------------------------
  -- `U ×ˢ V` is an open subset of the required closure, hence
  -- contained in its interior.
  ------------------------------------------------------------------
  have h_into :
      (U ×ˢ V) ⊆ interior (closure (interior (Set.prod A B))) :=
    interior_maximal h_sub hUV_open
  exact h_into hpUV

theorem P1_equiv_symm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (e : X ≃ₜ Y) : P1 (e '' A) → P1 A := by
  intro hP1_image
  -- Transport the `P1` property along the inverse homeomorphism.
  have hP1_preimage : P1 (e.symm '' (e '' A)) :=
    P1_image_homeomorph (e := e.symm) (A := e '' A) hP1_image
  -- Identify `e.symm '' (e '' A)` with `A`.
  have h_eq : (e.symm '' (e '' A) : Set X) = A := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hxy⟩
      rcases hy with ⟨z, hzA, rfl⟩
      -- `hxy` is `e.symm (e z) = x`.
      have : z = x := by
        simpa [e.symm_apply_apply] using hxy
      simpa [this] using hzA
    · intro hxA
      refine ⟨e x, ?_, ?_⟩
      · exact ⟨x, hxA, rfl⟩
      · simp
  -- Prove the desired `P1` statement for `A`.
  intro x hxA
  -- `x` lies in `e.symm '' (e '' A)`.
  have hx_pre : x ∈ e.symm '' (e '' A) := by
    refine ⟨e x, ?_, ?_⟩
    · exact ⟨x, hxA, rfl⟩
    · simp
  -- Apply the transported `P1` property.
  have hx_cl : x ∈ closure (interior (e.symm '' (e '' A))) :=
    hP1_preimage hx_pre
  -- Reinterpret the result using the set equality obtained above.
  simpa [h_eq] using hx_cl

theorem P3_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P3 A → P3 B → P3 (Set.prod A B) := by
  intro hP3A hP3B
  intro p hp
  rcases hp with ⟨hpA, hpB⟩
  -- each coordinate enjoys `P3`
  have hA : p.1 ∈ interior (closure A) := hP3A hpA
  have hB : p.2 ∈ interior (closure B) := hP3B hpB
  -- neighbourhoods around each coordinate
  set U : Set X := interior (closure A) with hU
  set V : Set Y := interior (closure B) with hV
  have hU_open : IsOpen U := by
    simpa [hU] using isOpen_interior
  have hV_open : IsOpen V := by
    simpa [hV] using isOpen_interior
  -- open neighbourhood of `p`
  have hUV_open : IsOpen (U ×ˢ V) := hU_open.prod hV_open
  have hpUV : p ∈ U ×ˢ V := by
    have hpU : p.1 ∈ U := by
      simpa [hU] using hA
    have hpV : p.2 ∈ V := by
      simpa [hV] using hB
    exact ⟨hpU, hpV⟩
  -- show this neighbourhood is contained in the closure
  have h_sub : (U ×ˢ V) ⊆ closure (Set.prod A B) := by
    intro q hq
    rcases hq with ⟨hqU, hqV⟩
    have hq1 : q.1 ∈ closure A := interior_subset hqU
    have hq2 : q.2 ∈ closure B := interior_subset hqV
    have hq_prod : q ∈ (closure A) ×ˢ (closure B) := ⟨hq1, hq2⟩
    have h_cl_eq : closure (Set.prod A B) = (closure A) ×ˢ (closure B) := by
      simpa using closure_prod_eq
    simpa [h_cl_eq] using hq_prod
  -- hence it lies in the interior of the closure
  have h_into : (U ×ˢ V) ⊆ interior (closure (Set.prod A B)) :=
    interior_maximal h_sub hUV_open
  exact h_into hpUV

theorem P2_symm_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set Y} (e : X ≃ₜ Y) : P2 (e.symm '' A) ↔ P2 A := by
  constructor
  · intro hP2
    -- First transport the property along `e`.
    have h : P2 (e '' (e.symm '' A)) :=
      (P2_image_homeomorph (e := e) (A := e.symm '' A)) hP2
    -- Identify the transported set with `A`.
    have hset : (e '' (e.symm '' A) : Set Y) = A := by
      ext y
      constructor
      · intro hy
        rcases hy with ⟨x, hx, rfl⟩
        rcases hx with ⟨z, hzA, rfl⟩
        simpa [e.apply_symm_apply] using hzA
      · intro hyA
        exact ⟨e.symm y, ⟨y, hyA, rfl⟩, by
          simp⟩
    simpa [hset] using h
  · intro hP2A
    simpa using
      (P2_image_homeomorph (e := e.symm) (A := A)) hP2A

theorem P3_conv_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} : closure A = Set.univ → P3 (closure A) := by
  intro h_dense
  -- The closure of `closure A` is still `closure A`, hence also `univ`.
  have h_dense' : closure (closure A) = (Set.univ : Set X) := by
    simpa [closure_closure] using h_dense
  -- Apply the existing lemma for dense sets.
  have hP3 : P3 (closure A) := P3_of_dense (A := closure A) h_dense'
  simpa using hP3

theorem P3_preimage_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} {f : X → Y} (hf : Continuous f) : IsOpen B → P3 (f ⁻¹' B) := by
  intro hB_open
  -- The preimage of an open set under a continuous map is open.
  have hOpen : IsOpen (f ⁻¹' B) := hB_open.preimage hf
  -- Apply the lemma asserting that open sets satisfy `P3`.
  exact P3_of_open (X := X) (A := f ⁻¹' B) hOpen

theorem P3_image_homeomorph_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (e : X ≃ₜ Y) : P3 (e '' A) ↔ P3 A := by
  constructor
  · intro hP3Image
    have hTrans :
        P3 (e.symm '' (e '' A)) :=
      (P3_image_homeomorph (e := e.symm) (A := (e '' A))) hP3Image
    have hSet : (e.symm '' (e '' A) : Set X) = A := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨y, hy, hxy⟩
        rcases hy with ⟨z, hzA, rfl⟩
        have : z = x := by
          simpa [e.symm_apply_apply] using hxy
        simpa [this] using hzA
      · intro hxA
        refine ⟨e x, ?_, ?_⟩
        · exact ⟨x, hxA, rfl⟩
        · simp
    intro x hx
    have hxS : x ∈ (e.symm '' (e '' A)) := by
      simpa [hSet] using hx
    have hxInt : x ∈ interior (closure (e.symm '' (e '' A))) :=
      hTrans hxS
    simpa [hSet] using hxInt
  · intro hP3A
    exact (P3_image_homeomorph (e := e) (A := A)) hP3A

theorem P1_image_homeomorph_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (e : X ≃ₜ Y) : P1 (e '' A) ↔ P1 A := by
  constructor
  · intro hP1Image
    exact (P1_equiv_symm (e := e) (A := A)) hP1Image
  · intro hP1A
    exact (P1_image_homeomorph (e := e) (A := A)) hP1A

theorem P2_image_homeomorph_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (e : X ≃ₜ Y) : P2 (e '' A) ↔ P2 A := by
  constructor
  · intro hP2Image
    -- Transport the property along `e.symm`.
    have hTrans : P2 (e.symm '' (e '' A)) :=
      (P2_image_homeomorph (e := e.symm) (A := e '' A)) hP2Image
    -- Identify the transported set with `A`.
    have hSet : (e.symm '' (e '' A) : Set X) = A := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨y, hy, hxy⟩
        rcases hy with ⟨z, hzA, rfl⟩
        have : z = x := by
          simpa [e.symm_apply_apply] using hxy
        simpa [this] using hzA
      · intro hxA
        refine ⟨e x, ?_, ?_⟩
        · exact ⟨x, hxA, rfl⟩
        · simp
    -- Use the equality to obtain the desired `P2` statement for `A`.
    intro x hx
    have hxSet : x ∈ (e.symm '' (e '' A)) := by
      simpa [hSet] using hx
    have hxInt :
        x ∈ interior (closure (interior (e.symm '' (e '' A)))) :=
      hTrans hxSet
    simpa [hSet] using hxInt
  · intro hP2A
    exact (P2_image_homeomorph (e := e) (A := A)) hP2A

theorem P1_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P1 A → P1 B → P1 (Set.prod A B) := by
  intro hP1A hP1B
  intro p hp
  rcases hp with ⟨hpA, hpB⟩
  -- Apply `P1` to each coordinate.
  have hA : p.1 ∈ closure (interior A) := hP1A hpA
  have hB : p.2 ∈ closure (interior B) := hP1B hpB
  ------------------------------------------------------------------
  -- `p` lies in the product of the two closures.
  ------------------------------------------------------------------
  have h_prod : p ∈ (closure (interior A)) ×ˢ (closure (interior B)) :=
    ⟨hA, hB⟩
  -- Identify this product with a closure of a product.
  have h_cl_eq :
      closure ((interior A) ×ˢ (interior B)) =
        (closure (interior A)) ×ˢ (closure (interior B)) := by
    simpa using closure_prod_eq
  have h_cl_prod :
      p ∈ closure ((interior A) ×ˢ (interior B)) := by
    simpa [h_cl_eq] using h_prod
  ------------------------------------------------------------------
  -- The product of interiors is contained in the interior of the product.
  ------------------------------------------------------------------
  have h_subset_int :
      ((interior A) ×ˢ (interior B)) ⊆ interior (Set.prod A B) := by
    apply interior_maximal
    · intro q hq
      rcases hq with ⟨hq1, hq2⟩
      exact ⟨interior_subset hq1, interior_subset hq2⟩
    · exact (isOpen_interior.prod isOpen_interior)
  -- Taking closures preserves inclusions.
  have h_closure_subset :
      closure ((interior A) ×ˢ (interior B)) ⊆
        closure (interior (Set.prod A B)) :=
    closure_mono h_subset_int
  ------------------------------------------------------------------
  -- Conclude.
  ------------------------------------------------------------------
  exact h_closure_subset h_cl_prod

theorem P1_preimage_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} {f : X → Y} : Continuous f → IsOpen B → P1 (f ⁻¹' B) := by
  intro hf hB
  -- The preimage is open since `f` is continuous and `B` is open.
  have hOpen : IsOpen (f ⁻¹' B) := hB.preimage hf
  -- Open sets satisfy `P3`.
  have hP3 : P3 (f ⁻¹' B) :=
    P3_of_open (X := X) (A := f ⁻¹' B) hOpen
  -- For open sets, `P1` is equivalent to `P3`.
  exact ((P1_iff_P3_of_open (X := X) (A := f ⁻¹' B) hOpen).2) hP3

theorem P3_prod₃ {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : P3 A → P3 B → P3 C → P3 (Set.prod A (Set.prod B C)) := by
  intro hP3A hP3B hP3C
  have hBC : P3 (Set.prod B C) :=
    P3_prod (A := B) (B := C) hP3B hP3C
  have hABC : P3 (Set.prod A (Set.prod B C)) :=
    P3_prod (A := A) (B := Set.prod B C) hP3A hBC
  exact hABC

theorem P1_dense_subset {X : Type*} [TopologicalSpace X] {A B : Set X} : A ⊆ B → closure A = closure B → P1 A → P1 B := by
  intro hAB hClos hP1
  intro x hxB
  -- Step 1: `x` lies in `closure A` (via the equality of closures).
  have hx_clA : x ∈ closure A := by
    have : x ∈ closure B := subset_closure hxB
    simpa [hClos] using this
  -- Step 2: `closure (interior A) = closure A` (from `P1 A`).
  have h_cl_eq : closure (interior A) = closure A :=
    (P1_iff_closure_eq (A := A)).1 hP1
  have hx_cl_intA : x ∈ closure (interior A) := by
    simpa [h_cl_eq] using hx_clA
  -- Step 3: `closure (interior A) ⊆ closure (interior B)` (since `A ⊆ B`).
  have hx_cl_intB : x ∈ closure (interior B) := by
    have h_subset : closure (interior A) ⊆ closure (interior B) := by
      exact closure_mono (interior_mono hAB)
    exact h_subset hx_cl_intA
  exact hx_cl_intB

theorem P3_interior_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P3 (interior A) := by
  intro hP2
  have hP2Int : P2 (interior A) := P2_interior (A := A) hP2
  exact (P2_subset_P3 (A := interior A) hP2Int)

theorem P1_of_open {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → P1 A := by
  intro hA
  have hP3 : P3 A := P3_of_open (X := X) (A := A) hA
  exact (P1_iff_P3_of_open (X := X) (A := A) hA).2 hP3

theorem P2_preimage_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} {f : X → Y} : Continuous f → IsOpen B → P2 (f ⁻¹' B) := by
  intro hf hB
  have hOpen : IsOpen (f ⁻¹' B) := hB.preimage hf
  exact P2_of_open (X := X) (A := f ⁻¹' B) hOpen

theorem P1_prod₃ {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : P1 A → P1 B → P1 C → P1 (Set.prod A (Set.prod B C)) := by
  intro hP1A hP1B hP1C
  -- obtain `P1` for `B ×ˢ C`
  have hBC : P1 (Set.prod B C) :=
    P1_prod (X := Y) (Y := Z) (A := B) (B := C) hP1B hP1C
  -- combine with `A`
  have hABC : P1 (Set.prod A (Set.prod B C)) :=
    P1_prod (X := X) (Y := Y × Z) (A := A) (B := Set.prod B C) hP1A hBC
  exact hABC

theorem P2_prod₃ {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : P2 A → P2 B → P2 C → P2 (Set.prod A (Set.prod B C)) := by
  intro hP2A hP2B hP2C
  -- obtain `P2` for `B ×ˢ C`
  have hBC : P2 (Set.prod B C) :=
    P2_prod (X := Y) (Y := Z) (A := B) (B := C) hP2B hP2C
  -- combine with `A`
  have hABC : P2 (Set.prod A (Set.prod B C)) :=
    P2_prod (X := X) (Y := Y × Z) (A := A) (B := Set.prod B C) hP2A hBC
  exact hABC

theorem P1_prod_swap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P1 (Set.prod A B) → P1 (Set.prod B A) := by
  intro hP1
  ----------------------------------------------------------------
  -- Step 1: transport the `P1` property along the swap homeomorphism.
  ----------------------------------------------------------------
  have hImage :
      P1 ((Homeomorph.prodComm X Y) '' (Set.prod A B)) :=
    P1_image_homeomorph
      (e := Homeomorph.prodComm X Y) (A := Set.prod A B) hP1
  ----------------------------------------------------------------
  -- Step 2: identify that image with `B ×ˢ A`.
  ----------------------------------------------------------------
  have hImage_eq :
      ((Homeomorph.prodComm X Y) '' (Set.prod A B) :
        Set (Y × X)) = Set.prod B A := by
    ext z
    constructor
    · -- `z` comes from the image
      rintro ⟨p, hpAB, rfl⟩
      rcases hpAB with ⟨hpA, hpB⟩
      exact ⟨hpB, hpA⟩
    · -- conversely, start with `z ∈ B ×ˢ A`
      intro hz
      rcases z with ⟨b, a⟩
      have hz' : (b, a) ∈ Set.prod B A := hz
      rcases hz' with ⟨hb, ha⟩
      refine ⟨(a, b), ?_, rfl⟩
      exact ⟨ha, hb⟩
  ----------------------------------------------------------------
  -- Step 3: rewrite and conclude.
  ----------------------------------------------------------------
  exact (hImage_eq ▸ hImage)

theorem P2_prod_swap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P2 (Set.prod A B) → P2 (Set.prod B A) := by
  intro hP2AB
  ----------------------------------------------------------------
  -- Step 1: transport the `P2` property along the swap homeomorphism.
  ----------------------------------------------------------------
  have hImage :
      P2 ((Homeomorph.prodComm X Y) '' (Set.prod A B)) :=
    P2_image_homeomorph
      (e := Homeomorph.prodComm X Y) (A := Set.prod A B) hP2AB
  -- The underlying map of `prodComm` is `Prod.swap`, so we rewrite.
  have hImage' : P2 (Prod.swap '' (Set.prod A B)) := by
    simpa using hImage
  ----------------------------------------------------------------
  -- Step 2: identify this image with `B ×ˢ A`.
  ----------------------------------------------------------------
  have hSwap_eq :
      (Prod.swap '' (Set.prod A B) : Set (Y × X)) = Set.prod B A := by
    ext z
    constructor
    · rintro ⟨p, hpAB, rfl⟩
      rcases hpAB with ⟨hpA, hpB⟩
      exact ⟨hpB, hpA⟩
    · intro hz
      rcases z with ⟨b, a⟩
      rcases hz with ⟨hb, ha⟩
      exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
  ----------------------------------------------------------------
  -- Step 3: rewrite and conclude.
  ----------------------------------------------------------------
  simpa [hSwap_eq] using hImage'

theorem P3_prod_swap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P3 (Set.prod A B) → P3 (Set.prod B A) := by
  intro hP3
  -- Step 1: transport `P3` along the swap homeomorphism.
  have hImage :
      P3 ((Homeomorph.prodComm X Y) '' (Set.prod A B)) :=
    P3_image_homeomorph
      (e := Homeomorph.prodComm X Y) (A := Set.prod A B) hP3
  -- Step 2: identify that image with `B ×ˢ A`.
  have hImage_eq :
      ((Homeomorph.prodComm X Y) '' (Set.prod A B) :
        Set (Y × X)) = Set.prod B A := by
    ext z
    constructor
    · rintro ⟨p, hpAB, rfl⟩
      rcases hpAB with ⟨hpA, hpB⟩
      exact ⟨hpB, hpA⟩
    · intro hz
      rcases z with ⟨b, a⟩
      have hz' : (b, a) ∈ Set.prod B A := hz
      rcases hz' with ⟨hb, ha⟩
      refine ⟨(a, b), ?_, rfl⟩
      exact ⟨ha, hb⟩
  -- Step 3: rewrite and conclude.
  exact (hImage_eq ▸ hImage)

theorem P1_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : P1 A → P1 (Set.prod A (Set.univ : Set Y)) := by
  intro hP1A
  have hP1_univ : P1 (Set.univ : Set Y) := P1_univ (X := Y)
  simpa using
    (P1_prod (X := X) (Y := Y) (A := A) (B := (Set.univ : Set Y)) hP1A hP1_univ)

theorem P2_has_closed_subset {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → ∃ C : Set X, IsClosed C ∧ C ⊆ A ∧ P2 C := by
  intro _
  exact
    ⟨(∅ : Set X), isClosed_empty, Set.empty_subset _, P2_empty (X := X)⟩

theorem P1_of_closed_dense {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → closure A = Set.univ → P1 A := by
  intro hClosed hDense
  -- Since `A` is closed, `closure A = A`.
  have hA_closure : closure A = A := hClosed.closure_eq
  -- Hence `A = univ`.
  have hA_univ : (A : Set X) = Set.univ := by
    calc
      A = closure A := (hA_closure).symm
      _ = Set.univ := hDense
  -- Establish the `P1` property.
  intro x hxA
  -- Interpret `hxA` as membership in `univ`.
  have hx_univ : x ∈ (Set.univ : Set X) := by
    simpa [hA_univ] using hxA
  -- Rewrite the goal using `A = univ`.
  simpa [hA_univ, interior_univ, closure_univ] using hx_univ

theorem P2_compact_subsets_are_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : (∀ C, C ⊆ A → IsCompact C → P2 C) → P1 A := by
  intro h
  -- We must show: `A ⊆ closure (interior A)`.
  intro x hxA
  ----------------------------------------------------------------
  -- 1. Apply the hypothesis to the compact singleton `{x}`.
  ----------------------------------------------------------------
  have h_subset_single : ({x} : Set X) ⊆ A := by
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy] ; exact hxA
  have h_compact_single : IsCompact ({x} : Set X) := isCompact_singleton
  have hP2_single : P2 ({x} : Set X) :=
    h ({x}) h_subset_single h_compact_single
  -- Hence `x` belongs to the interior of the closure of the interior
  -- of its singleton.
  have hx_in :
      x ∈ interior (closure (interior ({x} : Set X))) := by
    have : x ∈ ({x} : Set X) := by simp
    exact hP2_single this
  ----------------------------------------------------------------
  -- 2. Show that `interior {x}` is non-empty (otherwise contradiction).
  ----------------------------------------------------------------
  have hInt_nonempty : (interior ({x} : Set X)).Nonempty := by
    by_contra hcontr
    have hInt_empty :
        interior ({x} : Set X) = (∅ : Set X) :=
      Set.not_nonempty_iff_eq_empty.1 hcontr
    have : x ∈ (∅ : Set X) := by
      simpa [hInt_empty, closure_empty, interior_empty] using hx_in
    simpa using this
  -- Obtain a point `y` in `interior {x}`; necessarily `y = x`.
  rcases hInt_nonempty with ⟨y, hyInt⟩
  have hy_eq : y = x := by
    have : y ∈ ({x} : Set X) := interior_subset hyInt
    simpa [Set.mem_singleton_iff] using this
  have hx_int_single : x ∈ interior ({x} : Set X) := by
    simpa [hy_eq] using hyInt
  ----------------------------------------------------------------
  -- 3. `interior {x}` sits inside `interior A`, so `x ∈ interior A`.
  ----------------------------------------------------------------
  have h_int_subset : interior ({x} : Set X) ⊆ interior A := by
    apply interior_mono
    exact h_subset_single
  have hx_intA : x ∈ interior A := h_int_subset hx_int_single
  ----------------------------------------------------------------
  -- 4. Conclude `x ∈ closure (interior A)`.
  ----------------------------------------------------------------
  exact subset_closure hx_intA

theorem P1_of_exhaustion {X : Type*} [TopologicalSpace X] {A : Set X} (K : ℕ → Set X) : (∀ n, K n ⊆ K (n + 1)) → (⋃ n, K n) = A → (∀ n, P1 (K n)) → P1 A := by
  intro hMono hUnion hP1K
  -- touch `hMono` to avoid an unused-argument warning
  have _ := hMono 0
  intro x hxA
  -- Rewrite `hxA` using the union identity.
  have hxUnion : x ∈ ⋃ n, K n := by
    simpa [hUnion] using hxA
  -- Pick an index with `x ∈ K n`.
  rcases Set.mem_iUnion.1 hxUnion with ⟨n, hxKn⟩
  -- Apply the `P1` property for `K n`.
  have hP1n : P1 (K n) := hP1K n
  have hx_cl : x ∈ closure (interior (K n)) := hP1n hxKn
  -- Show `interior (K n) ⊆ interior A`.
  have hKn_subset_A : (K n : Set X) ⊆ A := by
    intro y hy
    have : (y : X) ∈ (⋃ m, K m) := by
      exact Set.mem_iUnion.2 ⟨n, hy⟩
    simpa [hUnion] using this
  have hSubset : interior (K n) ⊆ interior A :=
    interior_mono hKn_subset_A
  -- Taking closures preserves inclusions.
  have hx_clA : x ∈ closure (interior A) :=
    (closure_mono hSubset) hx_cl
  exact hx_clA

theorem P3_union_distrib {X : Type*} [TopologicalSpace X] {A B C : Set X} : P3 (A ∪ (B ∩ C)) ↔ P3 ((A ∪ B) ∩ (A ∪ C)) := by
  simpa [Set.union_inter_distrib_left]

theorem P1_prod_assoc {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : P1 (Set.prod (Set.prod A B) C) ↔ P1 (Set.prod A (Set.prod B C)) := by
  -- Abbreviate the associativity homeomorphism.
  let e := Homeomorph.prodAssoc X Y Z
  ------------------------------------------------------------------
  -- 1.  Identify the image of `(A ×ˢ B) ×ˢ C` under `e`.
  ------------------------------------------------------------------
  have hImage :
      (e '' (Set.prod (Set.prod A B) C) :
          Set (X × (Y × Z))) = Set.prod A (Set.prod B C) := by
    ext x
    constructor
    · -- `x` comes from the image.
      rintro ⟨p, hp, rfl⟩
      rcases p with ⟨⟨a, b⟩, c⟩
      rcases hp with ⟨⟨ha, hb⟩, hc⟩
      exact ⟨ha, ⟨hb, hc⟩⟩
    · -- Conversely, start with `x ∈ A ×ˢ (B ×ˢ C)`.
      intro hx
      rcases x with ⟨a, bc⟩
      rcases bc with ⟨b, c⟩
      rcases hx with ⟨ha, ⟨hb, hc⟩⟩
      refine ⟨((a, b), c), ?_, ?_⟩
      · exact ⟨⟨ha, hb⟩, hc⟩
      · -- `e ((a, b), c) = (a, (b, c))` by definition.
        rfl
  ------------------------------------------------------------------
  -- 2.  Transport the `P1` property along the homeomorphism and
  --     rewrite using `hImage`.
  ------------------------------------------------------------------
  have hEquiv :
      P1 (Set.prod (Set.prod A B) C) ↔ P1 (Set.prod A (Set.prod B C)) := by
    -- `P1 (e '' S) ↔ P1 S`
    have h :=
      (P1_image_homeomorph_iff
          (e := e)
          (A := Set.prod (Set.prod A B) C))
    -- Rewrite the left‐hand side via `hImage` and reverse the equivalence.
    simpa [hImage] using h.symm
  ------------------------------------------------------------------
  -- 3.  Conclude.
  ------------------------------------------------------------------
  simpa using hEquiv

theorem P3_constant_map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {c : Y} : P3 ({x : X | True}) := by
  simpa using (P3_univ (X := X))

theorem P1_sigma {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] {A : ∀ i, Set (X i)} : (∀ i, P1 (A i)) → P1 {x : Σ i, X i | x.2 ∈ A x.1} := by
  classical
  intro hP1
  -- `S` is the σ–type set we are interested in.
  intro x hx
  rcases x with ⟨i, a⟩
  -- Interpret the membership hypothesis in the fibre `i`.
  have ha : a ∈ A i := by
    simpa using hx
  -- Apply the `P1` property in the fibre.
  have h_cl_fibre : a ∈ closure (interior (A i)) := (hP1 i) ha
  ------------------------------------------------------------------
  -- Goal: `(i , a)` belongs to `closure (interior S)`.
  ------------------------------------------------------------------
  have h_closure :
      (⟨i, a⟩ : Σ j, X j) ∈
        closure (interior {y : Σ j, X j | y.2 ∈ A y.1}) := by
    -- Neighbourhood characterisation of the closure.
    apply (mem_closure_iff).2
    intro U hUopen hUa
    ----------------------------------------------------------------
    -- Slice the neighbourhood `U` in the fibre `i`.
    ----------------------------------------------------------------
    let V : Set (X i) := {y | (⟨i, y⟩ : Σ j, X j) ∈ U}
    have hVopen : IsOpen V := by
      have hSlice := (isOpen_sigma_iff).1 hUopen i
      simpa [V] using hSlice
    have haV : a ∈ V := by
      have : (⟨i, a⟩ : Σ j, X j) ∈ U := hUa
      simpa [V] using this
    ----------------------------------------------------------------
    -- Use the closure property in the fibre to get a point in
    -- `V ∩ interior (A i)`.
    ----------------------------------------------------------------
    have h_nonempty : ((V ∩ interior (A i)) : Set (X i)).Nonempty :=
      (mem_closure_iff).1 h_cl_fibre V hVopen haV
    rcases h_nonempty with ⟨b, hbV, hbIntAi⟩
    ----------------------------------------------------------------
    -- 1.  `(i , b)` lies in `U`.
    ----------------------------------------------------------------
    have hbU : (⟨i, b⟩ : Σ j, X j) ∈ U := by
      have : b ∈ V := hbV
      simpa [V] using this
    ----------------------------------------------------------------
    -- 2.  `(i , b)` lies in `interior S`.
    ----------------------------------------------------------------
    -- Define the auxiliary open set
    let S₂ : Set (Σ j, X j) := {y | y.2 ∈ interior (A y.1)}
    -- `S₂` is open:
    have hS₂_open : IsOpen S₂ := by
      -- Check the slices of `S₂`.
      have hSlices :
          ∀ j, IsOpen {y : X j | (⟨j, y⟩ : Σ k, X k) ∈ S₂} := by
        intro j
        have hEq :
            {y : X j | (⟨j, y⟩ : Σ k, X k) ∈ S₂} = interior (A j) := by
          ext y; simp [S₂]
        simpa [hEq] using isOpen_interior
      simpa [S₂] using (isOpen_sigma_iff).2 hSlices
    -- `S₂ ⊆ S`, hence `S₂ ⊆ interior S`.
    have hS₂_sub :
        (S₂ : Set (Σ j, X j)) ⊆
          {y : Σ j, X j | y.2 ∈ A y.1} := by
      intro y hy
      dsimp [S₂] at hy
      dsimp
      exact (interior_subset : interior (A y.1) ⊆ A y.1) hy
    have hS₂_to_int :
        (S₂ : Set (Σ j, X j)) ⊆
          interior {y : Σ j, X j | y.2 ∈ A y.1} :=
      interior_maximal hS₂_sub hS₂_open
    -- `(i , b)` belongs to `S₂`.
    have hbS₂ : (⟨i, b⟩ : Σ j, X j) ∈ S₂ := by
      dsimp [S₂]; simpa [hbIntAi]
    -- Hence `(i , b)` is in `interior S`.
    have hbIntS :
        (⟨i, b⟩ : Σ j, X j) ∈
          interior {y : Σ j, X j | y.2 ∈ A y.1} :=
      hS₂_to_int hbS₂
    -- Provide the required witness in `U ∩ interior S`.
    exact ⟨⟨i, b⟩, hbU, hbIntS⟩
  -- Conclude.
  simpa using h_closure

theorem P2_iSup_family {X : Type*} [TopologicalSpace X] {ι : Sort _} {F : ι → Set X} : (∀ i, P2 (F i)) → P2 (⋃ i, F i) := by
  intro h
  ------------------------------------------------------------------
  -- 1.  Every set in `Set.range F` satisfies `P2`.
  ------------------------------------------------------------------
  have hAll : ∀ A : Set X, A ∈ Set.range F → P2 A := by
    intro A hA
    rcases hA with ⟨i, rfl⟩
    exact h i
  ------------------------------------------------------------------
  -- 2.  Apply the `sUnion` lemma for `P2`.
  ------------------------------------------------------------------
  have hP2_range : P2 (⋃₀ Set.range F) :=
    P2_sUnion (X := X) (𝒜 := Set.range F) hAll
  ------------------------------------------------------------------
  -- 3.  Identify `⋃₀ Set.range F` with `⋃ i, F i`.
  ------------------------------------------------------------------
  have h_eq : (⋃₀ Set.range F : Set X) = ⋃ i, F i := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
      rcases hA_mem with ⟨i, rfl⟩
      exact Set.mem_iUnion.2 ⟨i, hxA⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hxFi⟩
      exact Set.mem_sUnion.2 ⟨F i, ⟨i, rfl⟩, hxFi⟩
  ------------------------------------------------------------------
  -- 4.  Transfer the result through the equality.
  ------------------------------------------------------------------
  simpa [h_eq] using hP2_range

theorem P1_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → interior (closure A) ⊆ closure (interior A) := by
  intro hP1
  intro x hx
  -- `x` lies in `closure A` because it lies in `interior (closure A)`.
  have hx_clA : x ∈ closure A := interior_subset hx
  -- From `P1 A`, we have `A ⊆ closure (interior A)`.
  -- Taking closures preserves inclusions.
  have h_subset : closure A ⊆ closure (interior A) := by
    have hA : (A : Set X) ⊆ closure (interior A) := hP1
    have h' : closure A ⊆ closure (closure (interior A)) :=
      closure_mono hA
    simpa [closure_closure] using h'
  exact h_subset hx_clA

theorem P2_union₃ {X : Type*} [TopologicalSpace X] {A B C : Set X} : P2 A → P2 B → P2 C → P2 (A ∪ B ∪ C) := by
  intro hP2A hP2B hP2C
  have hAB : P2 (A ∪ B) := P2_union hP2A hP2B
  have hABC : P2 ((A ∪ B) ∪ C) := P2_union hAB hP2C
  simpa [Set.union_assoc] using hABC

theorem P3_of_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : P3 A := by
  classical
  by_cases hA : (A : Set X) = ∅
  · -- If `A` is empty, use the previously proved lemma.
    simpa [hA] using (P3_empty (X := X))
  · -- Otherwise, `A` is non-empty.
    have h_nonempty : (A : Set X).Nonempty :=
      Set.nonempty_iff_ne_empty.2 hA
    rcases h_nonempty with ⟨x₀, hx₀A⟩
    -- Show that `closure A = univ`.
    have h_closure_univ : closure A = (Set.univ : Set X) := by
      ext y
      constructor
      · intro _; simp
      · intro _
        -- In a subsingleton, every point equals `x₀`.
        have h_eq : y = x₀ := Subsingleton.elim y x₀
        have hx₀_cl : x₀ ∈ closure A := subset_closure hx₀A
        simpa [h_eq] using hx₀_cl
    -- Conclude using `P3_of_dense`.
    exact P3_of_dense (X := X) (A := A) h_closure_univ

theorem P2_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : P2 A → P2 (Set.prod A (Set.univ : Set Y)) := by
  intro hP2A
  have hP2_univ : P2 (Set.univ : Set Y) := P2_univ (X := Y)
  simpa using
    (P2_prod (X := X) (Y := Y) (A := A) (B := (Set.univ : Set Y)) hP2A hP2_univ)

theorem P2_Union_inf {X : Type*} [TopologicalSpace X] {ι : Sort _} {F : ι → Set X} : (∀ i, P2 (F i)) → P2 (⋃ i, F i) := by
  intro h
  simpa using (P2_iSup_family (X := X) (F := F) h)

theorem P3_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : P3 A → P3 (Set.prod A (Set.univ : Set Y)) := by
  intro hP3A
  have hP3_univ : P3 (Set.univ : Set Y) := P3_univ (X := Y)
  simpa using
    (P3_prod (X := X) (Y := Y) (A := A) (B := (Set.univ : Set Y)) hP3A hP3_univ)

theorem P1_prod_left_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} : P1 B → P1 (Set.prod (Set.univ : Set X) B) := by
  intro hP1B
  have hP1_univ : P1 (Set.univ : Set X) := P1_univ (X := X)
  simpa using
    (P1_prod
        (X := X) (Y := Y)
        (A := (Set.univ : Set X)) (B := B)
        hP1_univ hP1B)

theorem P2_prod_left_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} : P2 B → P2 (Set.prod (Set.univ : Set X) B) := by
  intro hP2B
  have hP2_univ : P2 (Set.univ : Set X) := P2_univ (X := X)
  simpa using
    (P2_prod
        (X := X) (Y := Y)
        (A := (Set.univ : Set X)) (B := B)
        hP2_univ hP2B)

theorem P3_prod_left_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} : P3 B → P3 (Set.prod (Set.univ : Set X) B) := by
  intro hP3B
  have hP3_univ : P3 (Set.univ : Set X) := P3_univ (X := X)
  simpa using
    (P3_prod
        (X := X) (Y := Y)
        (A := (Set.univ : Set X)) (B := B)
        hP3_univ hP3B)

theorem P3_interior_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P3 (interior (A ∪ B)) ↔ P3 (interior A ∪ interior B) := by
  -- Both sets are open, hence automatically satisfy `P3`.
  have hOpen₁ : IsOpen (interior (A ∪ B)) := isOpen_interior
  have hOpen₂ : IsOpen (interior A ∪ interior B) :=
    (isOpen_interior : IsOpen (interior A)).union
      (isOpen_interior : IsOpen (interior B))
  have hP3₁ : P3 (interior (A ∪ B)) :=
    P3_of_open (X := X) (A := interior (A ∪ B)) hOpen₁
  have hP3₂ : P3 (interior A ∪ interior B) :=
    P3_of_open (X := X) (A := interior A ∪ interior B) hOpen₂
  exact ⟨fun _ => hP3₂, fun _ => hP3₁⟩

theorem P3_iff_P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : interior A = Set.univ) : P3 A ↔ P2 A := by
  constructor
  · intro _hP3
    exact P2_of_dense_interior (X := X) (A := A) h
  · intro hP2
    exact P2_subset_P3 (X := X) (A := A) hP2

theorem P2_prod_assoc {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : P2 (Set.prod (Set.prod A B) C) ↔ P2 (Set.prod A (Set.prod B C)) := by
  -- Abbreviate the associativity homeomorphism.
  let e := Homeomorph.prodAssoc X Y Z
  -- Identify the image of `(A ×ˢ B) ×ˢ C` under `e`.
  have hImage :
      ((e '' (Set.prod (Set.prod A B) C)) :
        Set (X × (Y × Z))) = Set.prod A (Set.prod B C) := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      rcases p with ⟨⟨a, b⟩, c⟩
      rcases hp with ⟨⟨ha, hb⟩, hc⟩
      exact ⟨ha, ⟨hb, hc⟩⟩
    · intro hx
      rcases x with ⟨a, bc⟩
      rcases bc with ⟨b, c⟩
      rcases hx with ⟨ha, ⟨hb, hc⟩⟩
      exact ⟨((a, b), c), ⟨⟨ha, hb⟩, hc⟩, rfl⟩
  -- Transport the `P2` property along the homeomorphism and rewrite.
  have h :=
    (P2_image_homeomorph_iff
        (e := e)
        (A := Set.prod (Set.prod A B) C)).symm
  simpa [hImage] using h

theorem P3_prod_assoc {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : P3 (Set.prod (Set.prod A B) C) ↔ P3 (Set.prod A (Set.prod B C)) := by
  -- Abbreviate the associativity homeomorphism.
  let e := Homeomorph.prodAssoc X Y Z
  -- Identify the image of `(A ×ˢ B) ×ˢ C` under `e`.
  have hImage :
      ((e '' (Set.prod (Set.prod A B) C)) :
        Set (X × (Y × Z))) = Set.prod A (Set.prod B C) := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      rcases p with ⟨⟨a, b⟩, c⟩
      rcases hp with ⟨⟨ha, hb⟩, hc⟩
      exact ⟨ha, ⟨hb, hc⟩⟩
    · intro hx
      rcases x with ⟨a, bc⟩
      rcases bc with ⟨b, c⟩
      rcases hx with ⟨ha, ⟨hb, hc⟩⟩
      exact ⟨((a, b), c), ⟨⟨ha, hb⟩, hc⟩, rfl⟩
  -- Transport the `P3` property along the homeomorphism and rewrite.
  have h :=
    (P3_image_homeomorph_iff
        (e := e)
        (A := Set.prod (Set.prod A B) C)).symm
  simpa [hImage] using h

theorem P2_countable_union {X : Type*} [TopologicalSpace X] {F : ℕ → Set X} : (∀ n, P2 (F n)) → P2 (⋃ n, F n) := by
  intro h
  simpa using (P2_iSup_family (X := X) (F := F) h)

theorem P1_union_distrib {X : Type*} [TopologicalSpace X] {A B C : Set X} : P1 (A ∪ (B ∩ C)) ↔ P1 ((A ∪ B) ∩ (A ∪ C)) := by
  simpa [Set.union_inter_distrib_left]

theorem P1_iff_P2_of_closed_dense {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → closure A = Set.univ → (P1 A ↔ P2 A) := by
  intro hClosed hDense
  -- From closedness and density, deduce `A = univ`.
  have hA_univ : (A : Set X) = Set.univ := by
    have h_cl : closure A = A := hClosed.closure_eq
    simpa [h_cl] using hDense
  -- `P1` and `P2` both hold for `A` because `A = univ`.
  have hP1A : P1 A := by
    simpa [hA_univ] using (P1_univ (X := X))
  have hP2A : P2 A := by
    simpa [hA_univ] using (P2_univ (X := X))
  -- Conclude the equivalence.
  exact ⟨fun _ => hP2A, fun _ => hP1A⟩

theorem P1_iterate_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (interior (interior A)) := by
  intro x hx
  have h : x ∈ closure (interior (interior A)) := subset_closure hx
  simpa [interior_interior] using h

theorem P2_interior_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P2 (interior (A ∪ B)) ↔ P2 (interior A ∪ interior B) := by
  have hOpen1 : IsOpen (interior (A ∪ B)) := isOpen_interior
  have hOpen2 : IsOpen (interior A ∪ interior B) :=
    (isOpen_interior : IsOpen (interior A)).union
      (isOpen_interior : IsOpen (interior B))
  have h1 := (P2_iff_P3_of_open (X := X) (A := interior (A ∪ B)) hOpen1)
  have h2 := (P3_interior_union (X := X) (A := A) (B := B))
  have h3 := (P2_iff_P3_of_open
                (X := X) (A := (interior A ∪ interior B)) hOpen2)
  simpa using h1.trans (h2.trans h3.symm)

theorem P2_iff_P1_and_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A ↔ P1 A := by
  have hP2P3 : P2 A ↔ P3 A :=
    P2_iff_P3_of_open (X := X) (A := A) hA
  have hP1P3 : P1 A ↔ P3 A :=
    P1_iff_P3_of_open (X := X) (A := A) hA
  simpa using hP2P3.trans hP1P3.symm

theorem P2_Union_closed {X : Type*} [TopologicalSpace X] {F : ℕ → Set X} : (∀ n, IsClosed (F n)) → (∀ n, P2 (F n)) → P2 (⋃ n, F n) := by
  intro hClosed hP2
  -- touch `hClosed` to avoid an unused-argument warning
  have _ := hClosed 0
  simpa using (P2_iSup_family (X := X) (F := F) hP2)

theorem P2_prod_inf {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A₁ A₂ : Set X} {B₁ B₂ : Set Y} : P2 (A₁ ∩ A₂) → P2 (B₁ ∩ B₂) → P2 ((A₁ ∩ A₂) ×ˢ (B₁ ∩ B₂)) := by
  intro hP2A hP2B
  simpa using
    (P2_prod (X := X) (Y := Y)
      (A := A₁ ∩ A₂) (B := B₁ ∩ B₂) hP2A hP2B)

theorem P3_compl_of_closed' {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → P3 A → P3 (Aᶜ) := by
  intro hClosed hP3A
  -- touch `hP3A` to avoid an unused-argument warning
  have _ := hP3A
  -- the complement of a closed set is open
  have hOpen : IsOpen (Aᶜ : Set X) := (isOpen_compl_iff).2 hClosed
  -- open sets satisfy `P3`
  exact P3_of_open (X := X) (A := Aᶜ) hOpen

theorem P2_filter_basis {X : Type*} [TopologicalSpace X] {A : Set X} : (∀ x ∈ A, ∃ s, IsOpen s ∧ x ∈ s ∧ s ⊆ A) → P2 A := by
  intro h
  intro x hxA
  rcases h x hxA with ⟨s, hs_open, hx_s, hs_sub⟩
  -- `s` is an open subset of `A`, hence contained in `interior A`
  have hs_sub_int : s ⊆ interior A := by
    apply interior_maximal
    · exact hs_sub
    · exact hs_open
  -- therefore `x ∈ interior A`
  have hx_intA : x ∈ interior A := hs_sub_int hx_s
  -- `interior A` is an open subset of `closure (interior A)`
  have h_subset : interior A ⊆ interior (closure (interior A)) := by
    apply interior_maximal
    · exact subset_closure
    · exact isOpen_interior
  exact h_subset hx_intA