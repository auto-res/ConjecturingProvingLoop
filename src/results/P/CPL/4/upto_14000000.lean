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


theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A → Topology.P1 A := by
  intro hP2
  exact Set.Subset.trans hP2 interior_subset

theorem openSet_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P1 A := by
  simpa [P1, hA.interior_eq] using (subset_closure : (A : Set X) ⊆ closure A)

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P3 A) (hB : Topology.P3 B) : Topology.P3 (A ∪ B) := by
  dsimp [P3] at *
  refine
    Set.union_subset
      (Set.Subset.trans hA <|
        interior_mono <|
          closure_mono (by
            intro x hx
            exact Or.inl hx))
      (Set.Subset.trans hB <|
        interior_mono <|
          closure_mono (by
            intro x hx
            exact Or.inr hx))

theorem P1_iff_closure_interior_eq_closure {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A ↔ closure (interior A) = closure A := by
  constructor
  · intro hP1
    have h₁ : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : (interior A : Set X) ⊆ A)
    have h₂ : (closure A : Set X) ⊆ closure (interior A) :=
      closure_minimal hP1 isClosed_closure
    exact Set.Subset.antisymm h₁ h₂
  · intro h_eq
    have h : (A : Set X) ⊆ closure (interior A) := by
      have hA : (A : Set X) ⊆ closure A := subset_closure
      simpa [h_eq] using hA
    simpa [P1] using h

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P2 A) (hB : Topology.P2 B) : Topology.P2 (A ∪ B) := by
  dsimp [Topology.P2] at *
  refine Set.union_subset ?_ ?_
  ·
    have hMono : interior (closure (interior A)) ⊆ interior (closure (interior (A ∪ B))) := by
      have h1 : (interior A : Set X) ⊆ interior (A ∪ B) := by
        have hA_subset : (A : Set X) ⊆ A ∪ B := by
          intro x hx
          exact Or.inl hx
        exact interior_mono hA_subset
      have h2 : (closure (interior A) : Set X) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h1
      exact interior_mono h2
    exact Set.Subset.trans hA hMono
  ·
    have hMono : interior (closure (interior B)) ⊆ interior (closure (interior (A ∪ B))) := by
      have h1 : (interior B : Set X) ⊆ interior (A ∪ B) := by
        have hB_subset : (B : Set X) ⊆ A ∪ B := by
          intro x hx
          exact Or.inr hx
        exact interior_mono hB_subset
      have h2 : (closure (interior B) : Set X) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h1
      exact interior_mono h2
    exact Set.Subset.trans hB hMono

theorem P1_Union_family {ι : Sort _} {X : Type*} [TopologicalSpace X] {s : ι → Set X} (h : ∀ i, Topology.P1 (s i)) : Topology.P1 (⋃ i, s i) := by
  dsimp [Topology.P1] at *
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  have hPi : (s i : Set X) ⊆ closure (interior (s i)) := h i
  have hx_closure : x ∈ closure (interior (s i)) := hPi hxi
  have h_int_mono : interior (s i) ⊆ interior (⋃ j, s j) :=
    interior_mono (Set.subset_iUnion _ _)
  have h_closure_mono :
      closure (interior (s i)) ⊆ closure (interior (⋃ j, s j)) :=
    closure_mono h_int_mono
  exact h_closure_mono hx_closure

theorem P1_closed_iff_eq_closure {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P1 A ↔ A = closure (interior A) := by
  simpa [hA.closure_eq, eq_comm] using
    (P1_iff_closure_interior_eq_closure (X := X) (A := A))

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A → Topology.P3 A := by
  intro hP2
  dsimp [Topology.P2, Topology.P3] at *
  refine
    Set.Subset.trans hP2
      (interior_mono
        (closure_mono (interior_subset : (interior A : Set X) ⊆ A)))

theorem P2_Union_family {ι : Sort _} {X : Type*} [TopologicalSpace X] {s : ι → Set X} (h : ∀ i, Topology.P2 (s i)) : Topology.P2 (⋃ i, s i) := by
  dsimp [Topology.P2] at *
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  have hPi : (s i : Set X) ⊆ interior (closure (interior (s i))) := h i
  have hx₁ : x ∈ interior (closure (interior (s i))) := hPi hxi
  have h_int_mono : interior (s i) ⊆ interior (⋃ j, s j) :=
    interior_mono (Set.subset_iUnion _ _)
  have h_closure_mono :
      closure (interior (s i)) ⊆ closure (interior (⋃ j, s j)) :=
    closure_mono h_int_mono
  have h_interior_mono :
      interior (closure (interior (s i))) ⊆
        interior (closure (interior (⋃ j, s j))) :=
    interior_mono h_closure_mono
  exact h_interior_mono hx₁

theorem P3_iUnion_directed {ι : Sort _} {X : Type*} [TopologicalSpace X] (s : ι → Set X) (hdir : Directed (· ⊆ ·) s) (h : ∀ i, Topology.P3 (s i)) : Topology.P3 (⋃ i, s i) := by
  dsimp [Topology.P3] at *
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  have hPi : (s i : Set X) ⊆ interior (closure (s i)) := h i
  have hx₁ : x ∈ interior (closure (s i)) := hPi hxi
  have h_closure_mono : (closure (s i) : Set X) ⊆ closure (⋃ j, s j) :=
    closure_mono (Set.subset_iUnion _ _)
  have h_interior_mono :
      interior (closure (s i)) ⊆ interior (closure (⋃ j, s j)) :=
    interior_mono h_closure_mono
  exact h_interior_mono hx₁

theorem P3_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : Homeomorph X Y) {A : Set X} (hA : Topology.P3 A) : Topology.P3 (e '' A) := by
  -- Expand the definition of `P3`
  dsimp [Topology.P3] at hA ⊢
  intro y hy
  -- Choose a preimage point `x ∈ A` with `y = e x`
  rcases hy with ⟨x, hxA, rfl⟩
  -- From the hypothesis we know that `x` lies in `interior (closure A)`
  have hx : x ∈ interior (closure A) := hA hxA
  ----------------------------------------------------------------
  -- 1.  The auxiliary set `S = e '' interior (closure A)` is open
  ----------------------------------------------------------------
  have hS_open : IsOpen (e '' interior (closure A)) := by
    -- Identify `S` with a preimage under the continuous map `e.symm`
    have h_eq :
        (e '' interior (closure A) : Set _) =
          { y | e.symm y ∈ interior (closure A) } := by
      ext y
      constructor
      · rintro ⟨x, hx', rfl⟩
        simp [hx']
      · intro hy
        refine ⟨e.symm y, ?_, ?_⟩
        · simpa using hy
        · simpa using e.apply_symm_apply y
    -- The right-hand side is a preimage of an open set under a continuous map
    have h_pre :
        IsOpen { y | e.symm y ∈ interior (closure A) } := by
      have h_int_open : IsOpen (interior (closure A)) := isOpen_interior
      simpa [Set.preimage] using h_int_open.preimage e.symm.continuous
    simpa [h_eq] using h_pre
  ----------------------------------------------------------------
  -- 2.  `S` is contained in `closure (e '' A)`
  ----------------------------------------------------------------
  have hS_subset : (e '' interior (closure A) : Set _) ⊆ closure (e '' A) := by
    intro z hz
    rcases hz with ⟨x', hx'int, rfl⟩
    -- `x'` lies in `closure A`
    have hx'cl : x' ∈ closure A := interior_subset hx'int
    -- Show `e x'` is in the closure of the image
    have : e x' ∈ closure (e '' A) := by
      -- Neighbourhood characterisation of the closure
      apply (mem_closure_iff).2
      intro V hVopen hVmem
      -- Preimage of `V` under `e`
      have hUopen : IsOpen (e ⁻¹' V) := hVopen.preimage e.continuous
      have hxU : x' ∈ e ⁻¹' V := by
        simpa [Set.mem_preimage] using hVmem
      -- Since `x' ∈ closure A`, the intersection with `A` is non-empty
      have h_nonempty_pre : ((e ⁻¹' V) ∩ A).Nonempty := by
        have h_closure := (mem_closure_iff).1 hx'cl
        exact h_closure (e ⁻¹' V) hUopen hxU
      -- Map a witness through `e`
      rcases h_nonempty_pre with ⟨w, ⟨hw_preV, hwA⟩⟩
      have hwV : e w ∈ V := by
        simpa [Set.mem_preimage] using hw_preV
      have hwIm : e w ∈ e '' A := ⟨w, hwA, rfl⟩
      exact ⟨e w, And.intro hwV hwIm⟩
    exact this
  ----------------------------------------------------------------
  -- 3.  Maximality of the interior
  ----------------------------------------------------------------
  have hS_in_interior :
      (e '' interior (closure A) : Set _) ⊆
        interior (closure (e '' A)) :=
    interior_maximal hS_subset hS_open
  ----------------------------------------------------------------
  -- 4.  Our point belongs to `S`, hence to the desired interior
  ----------------------------------------------------------------
  have hy_in_S : e x ∈ e '' interior (closure A) := ⟨x, hx, rfl⟩
  exact hS_in_interior hy_in_S

theorem P3_closed_iff {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P3 A ↔ A = interior (closure A) := by
  -- Unfold the definition of `P3`
  dsimp [Topology.P3]
  -- For a closed set, `interior (closure A)` is contained in `A`
  have h_subset : (interior (closure A) : Set X) ⊆ A := by
    have h : (interior (closure A) : Set X) ⊆ closure A := interior_subset
    simpa [hA.closure_eq] using h
  constructor
  · -- `P3 A → A = interior (closure A)`
    intro hP3
    exact Set.Subset.antisymm hP3 h_subset
  · -- `A = interior (closure A) → P3 A`
    intro h_eq
    intro x hx
    -- Rewrite `hx : x ∈ A` using the given equality
    exact (h_eq ▸ hx)

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P1 A) (hB : Topology.P1 B) : Topology.P1 (A ∪ B) := by
  dsimp [Topology.P1] at *
  refine
    Set.union_subset
      (Set.Subset.trans hA <|
        closure_mono <|
          interior_mono (by
            intro x hx
            exact Or.inl hx))
      (Set.Subset.trans hB <|
        closure_mono <|
          interior_mono (by
            intro x hx
            exact Or.inr hx))

theorem P3_Union_family {ι : Sort _} {X : Type*} [TopologicalSpace X] {s : ι → Set X} (h : ∀ i, Topology.P3 (s i)) : Topology.P3 (⋃ i, s i) := by
  dsimp [Topology.P3] at *
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  have hPi : (s i : Set X) ⊆ interior (closure (s i)) := h i
  have hx₁ : x ∈ interior (closure (s i)) := hPi hxi
  have h_closure_mono : (closure (s i) : Set X) ⊆ closure (⋃ j, s j) :=
    closure_mono (Set.subset_iUnion _ _)
  have h_interior_mono :
      interior (closure (s i)) ⊆ interior (closure (⋃ j, s j)) :=
    interior_mono h_closure_mono
  exact h_interior_mono hx₁

theorem P2_iff_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A ↔ Topology.P1 A ∧ Topology.P3 A := by
  constructor
  · intro hP2
    exact ⟨P2_implies_P1 (A := A) hP2, P2_implies_P3 (A := A) hP2⟩
  · rintro ⟨hP1, hP3⟩
    dsimp [P2, P1, P3] at hP1 hP3 ⊢
    intro x hxA
    -- First: `x` lies in `interior (closure A)` by `P3`
    have hx_int_closureA : x ∈ interior (closure A) := hP3 hxA
    -- Second: `closure A ⊆ closure (interior A)` using `P1`
    have h_closure_subset : (closure A : Set X) ⊆ closure (interior A) :=
      closure_minimal hP1 isClosed_closure
    -- Hence the interiors satisfy the analogous inclusion
    have h_interior_mono :
        interior (closure A) ⊆ interior (closure (interior A)) :=
      interior_mono h_closure_subset
    -- Combine
    exact h_interior_mono hx_int_closureA

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Dense A) : Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hx
  simpa [hA.closure_eq, interior_univ]

theorem P1_empty {X : Type*} [TopologicalSpace X] : Topology.P1 (∅ : Set X) := by
  dsimp [P1]
  exact Set.empty_subset _

theorem P2_empty {X : Type*} [TopologicalSpace X] : Topology.P2 (∅ : Set X) := by
  dsimp [Topology.P2]
  exact Set.empty_subset _

theorem P3_empty {X : Type*} [TopologicalSpace X] : Topology.P3 (∅ : Set X) := by
  dsimp [Topology.P3]
  exact Set.empty_subset _

theorem P1_univ {X : Type*} [TopologicalSpace X] : Topology.P1 (Set.univ : Set X) := by
  simpa using
    (openSet_P1 (X := X) (A := (Set.univ : Set X)) isOpen_univ)

theorem P2_univ {X : Type*} [TopologicalSpace X] : Topology.P2 (Set.univ : Set X) := by
  dsimp [Topology.P2]
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P3_univ {X : Type*} [TopologicalSpace X] : Topology.P3 (Set.univ : Set X) := by
  dsimp [Topology.P3]
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P2_iUnion_directed {ι : Sort _} {X : Type*} [TopologicalSpace X] (s : ι → Set X) (hdir : Directed (· ⊆ ·) s) (h : ∀ i, Topology.P2 (s i)) : Topology.P2 (⋃ i, s i) := by
  simpa using (P2_Union_family (X := X) (s := s) h)

theorem P1_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : Homeomorph X Y) {A : Set X} (hA : Topology.P1 A) : Topology.P1 (e '' A) := by
  -- Unfold the definition of `P1`
  dsimp [Topology.P1] at hA ⊢
  -- Take a point of the image
  rintro y ⟨x, hxA, rfl⟩
  -- `x` lies in the closure of `interior A`
  have hx_cl : (x : X) ∈ closure (interior A) := hA hxA
  ----------------------------------------------------------------
  -- Auxiliary open set `S = e '' interior A`
  ----------------------------------------------------------------
  let S : Set Y := e '' interior A
  have hS_open : IsOpen (S) := by
    -- Identify `S` with a preimage of an open set under `e.symm`
    have h_eq : (S : Set Y) = { y | e.symm y ∈ interior A } := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        simp [hw]
      · intro hz
        refine ⟨e.symm z, ?_, ?_⟩
        · simpa using hz
        · simpa using e.apply_symm_apply z
    -- The right-hand side is open as the preimage of an open set
    have h_pre :
        IsOpen { y | e.symm y ∈ interior A } := by
      have : IsOpen (interior A) := isOpen_interior
      simpa [Set.preimage] using this.preimage e.symm.continuous
    simpa [h_eq] using h_pre
  ----------------------------------------------------------------
  -- `S` is contained in `interior (e '' A)`
  ----------------------------------------------------------------
  have hS_subset : (S : Set Y) ⊆ interior (e '' A) := by
    -- First, `S ⊆ e '' A`
    have hS_sub : (S : Set Y) ⊆ e '' A := by
      intro z hz
      rcases hz with ⟨w, hw, rfl⟩
      exact ⟨w, interior_subset hw, rfl⟩
    -- Maximality of the interior
    simpa using interior_maximal hS_sub hS_open
  ----------------------------------------------------------------
  -- Show `e x ∈ closure S`
  ----------------------------------------------------------------
  have h_ex_closure_S : e x ∈ closure (S) := by
    -- Use the filter characterisation of the closure
    apply (mem_closure_iff).2
    intro V hV_open hxV
    -- Preimage of `V` under `e`
    let U : Set X := e ⁻¹' V
    have hU_open : IsOpen U := hV_open.preimage e.continuous
    have hxU : x ∈ U := by
      change e x ∈ V at hxV
      simpa [U, Set.mem_preimage] using hxV
    -- `U ∩ interior A` is non-empty
    have h_nonempty : (U ∩ interior A).Nonempty := by
      have := (mem_closure_iff).1 hx_cl U hU_open hxU
      simpa [U] using this
    rcases h_nonempty with ⟨w, hwU, hw_int⟩
    -- Produce the required witness in `V ∩ S`
    have hwV : e w ∈ V := by
      have : w ∈ U := hwU
      simpa [U, Set.mem_preimage] using this
    have hwS : e w ∈ S := by
      exact ⟨w, hw_int, rfl⟩
    exact ⟨e w, And.intro hwV hwS⟩
  ----------------------------------------------------------------
  -- Monotonicity of the closure finishes the proof
  ----------------------------------------------------------------
  have h_closure_mono :
      closure (S) ⊆ closure (interior (e '' A)) :=
    closure_mono hS_subset
  exact h_closure_mono h_ex_closure_S

theorem P2_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : Homeomorph X Y) {A : Set X} (hA : Topology.P2 A) : Topology.P2 (e '' A) := by
  -- `A` satisfies both `P1` and `P3`, hence so does its image
  have hP1_img : Topology.P1 (e '' A) :=
    P1_image_homeomorph (e := e) (P2_implies_P1 (A := A) hA)
  have hP3_img : Topology.P3 (e '' A) :=
    P3_image_homeomorph (e := e) (P2_implies_P3 (A := A) hA)
  -- Use the characterisation `P2 ↔ P1 ∧ P3`
  exact (P2_iff_P1_and_P3 (A := e '' A)).2 ⟨hP1_img, hP3_img⟩

theorem P3_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : Homeomorph X Y) {B : Set Y} (hB : Topology.P3 B) : Topology.P3 (e ⁻¹' B) := by
  -- First, identify the preimage with the image under `e.symm`.
  have h_preimage : (e.symm '' B : Set X) = e ⁻¹' B := by
    ext x
    constructor
    · rintro ⟨y, hyB, rfl⟩
      simpa [Set.mem_preimage, e.apply_symm_apply] using hyB
    · intro hx
      refine ⟨e x, ?_, ?_⟩
      · simpa [Set.mem_preimage] using hx
      · simpa using e.symm_apply_apply x
  -- Apply the image lemma for `e.symm` and rewrite using the equality above.
  have hP3 : Topology.P3 (e.symm '' B) :=
    P3_image_homeomorph (e := e.symm) (A := B) hB
  simpa [h_preimage] using hP3

theorem openSet_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P2 A := by
  dsimp [Topology.P2]
  intro x hx
  -- `A` is an open neighbourhood of `x`
  have h_nhds : (closure (A : Set X)) ∈ 𝓝 x := by
    have h_mem : (A : Set X) ∈ 𝓝 x := IsOpen.mem_nhds hA hx
    exact Filter.mem_of_superset h_mem (subset_closure : (A : Set X) ⊆ closure A)
  have hx_int : x ∈ interior (closure A) :=
    (mem_interior_iff_mem_nhds).2 h_nhds
  simpa [hA.interior_eq] using hx_int

theorem P2_sUnion_family {ι : Sort _} {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (h : ∀ A ∈ 𝒜, Topology.P2 A) : Topology.P2 (⋃₀ 𝒜) := by
  -- Unfold the definition of `P2`
  dsimp [Topology.P2] at *
  intro x hx
  -- Pick a set `A ∈ 𝒜` with `x ∈ A`
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  -- `x` lies in `interior (closure (interior A))` by the hypothesis on `A`
  have hA_P2 : (A : Set X) ⊆ interior (closure (interior A)) := h A hA_mem
  have hx₁ : x ∈ interior (closure (interior A)) := hA_P2 hxA
  ----------------------------------------------------------------
  -- Monotonicity:  `interior (closure (interior A)) ⊆
  --                 interior (closure (interior ⋃₀ 𝒜))`
  ----------------------------------------------------------------
  -- First, `A ⊆ ⋃₀ 𝒜`
  have hA_subset_sUnion : (A : Set X) ⊆ ⋃₀ 𝒜 := by
    intro y hy
    exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
  -- Hence, `interior A ⊆ interior (⋃₀ 𝒜)`
  have h_int_subset :
      (interior A : Set X) ⊆ interior (⋃₀ 𝒜) :=
    interior_mono hA_subset_sUnion
  -- Taking closures, then interiors again
  have h_closure_subset :
      (closure (interior A) : Set X) ⊆ closure (interior (⋃₀ 𝒜)) :=
    closure_mono h_int_subset
  have h_interior_closure_subset :
      interior (closure (interior A)) ⊆
        interior (closure (interior (⋃₀ 𝒜))) :=
    interior_mono h_closure_subset
  ----------------------------------------------------------------
  -- Finish
  ----------------------------------------------------------------
  exact h_interior_closure_subset hx₁

theorem P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense (interior A)) : Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hx
  -- First, prove that `closure A = univ`
  have h_closureA : (closure (A : Set X)) = (Set.univ : Set X) := by
    -- `closure (interior A)` is the whole space by density
    have h_univ : (closure (interior A) : Set X) = Set.univ := h.closure_eq
    -- And `closure (interior A)` is contained in `closure A`
    have h_subset : (closure (interior A) : Set X) ⊆ closure A :=
      closure_mono (interior_subset : (interior A : Set X) ⊆ A)
    -- Hence `univ ⊆ closure A`
    have : (Set.univ : Set X) ⊆ closure A := by
      simpa [h_univ] using h_subset
    -- Conclude the equality
    exact Set.Subset.antisymm (by
      intro y hy
      trivial) this
  -- With `closure A = univ`, its interior is also `univ`
  simpa [h_closureA, interior_univ]

theorem openSet_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hx
  have hsubset : (A : Set X) ⊆ interior (closure A) :=
    interior_maximal (subset_closure : (A : Set X) ⊆ closure A) hA
  exact hsubset hx

theorem P3_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P3 A) (hB : Topology.P3 B) : Topology.P3 (Set.prod A B) := by
  -- Expand `P3` in the hypotheses and in the goal
  dsimp [Topology.P3] at hA hB ⊢
  intro p hp
  rcases hp with ⟨hpA, hpB⟩
  -- Coordinate-wise use of the hypotheses
  have hx : p.1 ∈ interior (closure A) := hA hpA
  have hy : p.2 ∈ interior (closure B) := hB hpB
  ----------------------------------------------------------------
  -- 1.  The open rectangle
  ----------------------------------------------------------------
  have h_open :
      IsOpen (Set.prod (interior (closure A)) (interior (closure B))) := by
    have h1 : IsOpen (interior (closure A)) := isOpen_interior
    have h2 : IsOpen (interior (closure B)) := isOpen_interior
    simpa using h1.prod h2
  ----------------------------------------------------------------
  -- 2.  The rectangle is contained in `closure (A × B)`
  ----------------------------------------------------------------
  have h_subset :
      (Set.prod (interior (closure A)) (interior (closure B)) : Set (X × Y)) ⊆
        closure (Set.prod A B) := by
    intro q hq
    rcases hq with ⟨hq₁, hq₂⟩
    have hq1_cl : q.1 ∈ closure A := interior_subset hq₁
    have hq2_cl : q.2 ∈ closure B := interior_subset hq₂
    have h_mem_prod : (q : X × Y) ∈ Set.prod (closure A) (closure B) :=
      And.intro hq1_cl hq2_cl
    have h_eq :
        (closure (Set.prod A B) : Set (X × Y)) =
          Set.prod (closure A) (closure B) := by
      simpa using
        (closure_prod_eq :
          closure (Set.prod A B) = Set.prod (closure A) (closure B))
    simpa [h_eq] using h_mem_prod
  ----------------------------------------------------------------
  -- 3.  Maximality of the interior
  ----------------------------------------------------------------
  have h_interior :
      (Set.prod (interior (closure A)) (interior (closure B)) : Set (X × Y)) ⊆
        interior (closure (Set.prod A B)) :=
    interior_maximal h_subset h_open
  ----------------------------------------------------------------
  -- 4.  Our point lies in the rectangle, hence in the desired interior
  ----------------------------------------------------------------
  have hp_rect :
      p ∈ Set.prod (interior (closure A)) (interior (closure B)) :=
    And.intro hx hy
  exact h_interior hp_rect

theorem P1_sUnion_family {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (h : ∀ A ∈ 𝒜, Topology.P1 A) : Topology.P1 (⋃₀ 𝒜) := by
  dsimp [Topology.P1] at *
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hA_P1 : (A : Set X) ⊆ closure (interior A) := h A hA_mem
  have hx₁ : x ∈ closure (interior A) := hA_P1 hxA
  have hA_subset_sUnion : (A : Set X) ⊆ ⋃₀ 𝒜 := by
    intro y hy
    exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
  have h_interior_subset :
      (interior A : Set X) ⊆ interior (⋃₀ 𝒜) :=
    interior_mono hA_subset_sUnion
  have h_closure_subset :
      (closure (interior A) : Set X) ⊆ closure (interior (⋃₀ 𝒜)) :=
    closure_mono h_interior_subset
  exact h_closure_subset hx₁

theorem P3_sUnion_family {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (h : ∀ A ∈ 𝒜, Topology.P3 A) : Topology.P3 (⋃₀ 𝒜) := by
  dsimp [Topology.P3] at *
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hA_P3 : (A : Set X) ⊆ interior (closure A) := h A hA_mem
  have hx₁ : x ∈ interior (closure A) := hA_P3 hxA
  have hA_subset_sUnion : (A : Set X) ⊆ ⋃₀ 𝒜 := by
    intro y hy
    exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
  have h_closure_subset :
      (closure A : Set X) ⊆ closure (⋃₀ 𝒜) :=
    closure_mono hA_subset_sUnion
  have h_interior_subset :
      (interior (closure A) : Set X) ⊆ interior (closure (⋃₀ 𝒜)) :=
    interior_mono h_closure_subset
  exact h_interior_subset hx₁

theorem P2_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : Homeomorph X Y) {B : Set Y} (hB : Topology.P2 B) : Topology.P2 (e ⁻¹' B) := by
  -- `B` satisfies both `P1` and `P3`
  have hP1B : Topology.P1 B := P2_implies_P1 (A := B) hB
  have hP3B : Topology.P3 B := P2_implies_P3 (A := B) hB
  ----------------------------------------------------------------
  -- 1.  Identify the preimage with an image under `e.symm`
  ----------------------------------------------------------------
  have h_eq : (e.symm '' B : Set X) = e ⁻¹' B := by
    ext x
    constructor
    · rintro ⟨y, hyB, rfl⟩
      simpa [Set.mem_preimage, e.apply_symm_apply] using hyB
    · intro hx
      refine ⟨e x, ?_, ?_⟩
      · simpa [Set.mem_preimage] using hx
      · simpa using e.symm_apply_apply x
  ----------------------------------------------------------------
  -- 2.  `P1` for the preimage
  ----------------------------------------------------------------
  have hP1_pre : Topology.P1 (e ⁻¹' B) := by
    have : Topology.P1 (e.symm '' B) :=
      P1_image_homeomorph (e := e.symm) (A := B) hP1B
    simpa [h_eq] using this
  ----------------------------------------------------------------
  -- 3.  `P3` for the preimage (already available)
  ----------------------------------------------------------------
  have hP3_pre : Topology.P3 (e ⁻¹' B) :=
    P3_preimage_homeomorph (e := e) (B := B) hP3B
  ----------------------------------------------------------------
  -- 4.  Combine via the characterisation of `P2`
  ----------------------------------------------------------------
  exact (P2_iff_P1_and_P3 (A := e ⁻¹' B)).2 ⟨hP1_pre, hP3_pre⟩

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense (interior A)) : Topology.P2 A := by
  dsimp [Topology.P2]
  intro x hx
  -- The closure of `interior A` is the whole space, by density.
  have h_closure : (closure (interior A) : Set X) = (Set.univ : Set X) :=
    h.closure_eq
  -- Hence its interior is also the whole space.
  have h_interior : (interior (closure (interior A)) : Set X) = Set.univ := by
    simpa [h_closure, interior_univ]
  -- The required inclusion now follows.
  simpa [h_interior] using (by
    trivial : x ∈ (Set.univ : Set X))

theorem P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P1 A) : Topology.P1 (interior A) := by
  simpa using openSet_P1 (X := X) (A := interior A) isOpen_interior

theorem P2_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P2 A) (hB : Topology.P2 B) : Topology.P2 (Set.prod A B) := by
  -- Obtain `P1` and `P3` for the individual factors
  have hP1A : Topology.P1 A := P2_implies_P1 (A := A) hA
  have hP1B : Topology.P1 B := P2_implies_P1 (A := B) hB
  have hP3A : Topology.P3 A := P2_implies_P3 (A := A) hA
  have hP3B : Topology.P3 B := P2_implies_P3 (A := B) hB
  ----------------------------------------------------------------
  -- `P3` for the product
  ----------------------------------------------------------------
  have hP3_prod : Topology.P3 (Set.prod A B) := P3_prod hP3A hP3B
  ----------------------------------------------------------------
  -- `P1` for the product
  ----------------------------------------------------------------
  have hP1_prod : Topology.P1 (Set.prod A B) := by
    dsimp [Topology.P1] at hP1A hP1B ⊢
    intro p hp
    rcases hp with ⟨hpA, hpB⟩
    -- Coordinates lie in the corresponding closures
    have hx : p.1 ∈ closure (interior A) := hP1A hpA
    have hy : p.2 ∈ closure (interior B) := hP1B hpB
    -- Hence the point lies in the product of the two closures
    have h_prod_closure :
        (p : X × Y) ∈ Set.prod (closure (interior A)) (closure (interior B)) :=
      ⟨hx, hy⟩
    -- Identify this product with a closure of a product
    have h_closure_eq :
        (closure (Set.prod (interior A) (interior B)) : Set (X × Y)) =
          Set.prod (closure (interior A)) (closure (interior B)) := by
      simpa using
        (closure_prod_eq :
          closure (Set.prod (interior A) (interior B)) =
            Set.prod (closure (interior A)) (closure (interior B)))
    have h_in_closure_prod :
        (p : X × Y) ∈ closure (Set.prod (interior A) (interior B)) := by
      simpa [h_closure_eq] using h_prod_closure
    ----------------------------------------------------------------
    -- The closure above is contained in `closure (interior (A × B))`
    ----------------------------------------------------------------
    have h_prod_subset :
        (Set.prod (interior A) (interior B) : Set (X × Y)) ⊆
          interior (Set.prod A B) := by
      -- Basic inclusion into `A × B`
      have h_simple :
          (Set.prod (interior A) (interior B) : Set (X × Y)) ⊆ Set.prod A B := by
        intro q hq
        rcases hq with ⟨ha, hb⟩
        exact ⟨interior_subset ha, interior_subset hb⟩
      -- The set on the left is open
      have h_open : IsOpen (Set.prod (interior A) (interior B)) := by
        have h1 : IsOpen (interior A) := isOpen_interior
        have h2 : IsOpen (interior B) := isOpen_interior
        simpa using h1.prod h2
      exact interior_maximal h_simple h_open
    have h_closure_subset :
        (closure (Set.prod (interior A) (interior B)) : Set (X × Y)) ⊆
          closure (interior (Set.prod A B)) :=
      closure_mono h_prod_subset
    exact h_closure_subset h_in_closure_prod
  ----------------------------------------------------------------
  -- Combine `P1` and `P3` via the characterisation of `P2`
  ----------------------------------------------------------------
  exact
    (P2_iff_P1_and_P3 (A := Set.prod A B)).2 ⟨hP1_prod, hP3_prod⟩

theorem P1_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : Homeomorph X Y) {B : Set Y} (hB : Topology.P1 B) : Topology.P1 (e ⁻¹' B) := by
  -- Step 1: identify the preimage with an image under `e.symm`
  have h_eq : (e.symm '' B : Set X) = e ⁻¹' B := by
    ext x
    constructor
    · rintro ⟨y, hyB, rfl⟩
      simpa [Set.mem_preimage, e.apply_symm_apply] using hyB
    · intro hx
      refine ⟨e x, ?_, ?_⟩
      · simpa [Set.mem_preimage] using hx
      · simpa using e.symm_apply_apply x
  -- Step 2: apply the image lemma for `e.symm`
  have hP1_image : Topology.P1 (e.symm '' B) :=
    P1_image_homeomorph (e := e.symm) (A := B) hB
  simpa [h_eq] using hP1_image

theorem P2_closed_iff {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P2 A ↔ A = interior (closure (interior A)) := by
  --------------------------------------------------------------------
  -- Auxiliary inclusion : `interior (closure (interior A)) ⊆ A`
  -- (it uses that `A` is closed).
  --------------------------------------------------------------------
  have h_subset :
      (interior (closure (interior A)) : Set X) ⊆ A := by
    intro x hx
    -- first, `x ∈ closure (interior A)`
    have hx_cl_int : x ∈ closure (interior A) := interior_subset hx
    -- monotonicity of `closure`
    have hx_clA : x ∈ closure A :=
      (closure_mono (interior_subset : (interior A : Set X) ⊆ A)) hx_cl_int
    -- since `A` is closed, `closure A = A`
    simpa [hA.closure_eq] using hx_clA
  --------------------------------------------------------------------
  -- Establish the equivalence.
  --------------------------------------------------------------------
  constructor
  · -- `P2 A → A = interior (closure (interior A))`
    intro hP2
    exact Set.Subset.antisymm hP2 h_subset
  · -- `A = interior (closure (interior A)) → P2 A`
    intro h_eq
    dsimp [Topology.P2]
    intro x hxA
    -- rewrite the membership using the given equality
    exact (h_eq ▸ hxA)

theorem P1_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P1 A) (hB : Topology.P1 B) : Topology.P1 (Set.prod A B) := by
  -- Unfold `P1` in the hypotheses and in the goal
  dsimp [Topology.P1] at hA hB ⊢
  intro p hp
  rcases hp with ⟨hpA, hpB⟩
  -- Apply the coordinate‐wise hypotheses
  have hx : p.1 ∈ closure (interior A) := hA hpA
  have hy : p.2 ∈ closure (interior B) := hB hpB
  -- Hence `p` belongs to the product of the two closures
  have h_prod :
      (p : X × Y) ∈ Set.prod (closure (interior A)) (closure (interior B)) :=
    And.intro hx hy
  -- Identify the latter with a closure of a product
  have h_closure_prod :
      (closure (Set.prod (interior A) (interior B)) : Set (X × Y)) =
        Set.prod (closure (interior A)) (closure (interior B)) := by
    simpa using
      (closure_prod_eq :
        closure (Set.prod (interior A) (interior B)) =
          Set.prod (closure (interior A)) (closure (interior B)))
  have hp_in_closure :
      (p : X × Y) ∈ closure (Set.prod (interior A) (interior B)) := by
    simpa [h_closure_prod] using h_prod
  ----------------------------------------------------------------
  -- Inclusion of the open rectangle into `interior (A × B)`
  ----------------------------------------------------------------
  have h_subset :
      (Set.prod (interior A) (interior B) : Set (X × Y)) ⊆
        interior (Set.prod A B) := by
    -- Basic inclusion into `A × B`
    have h_basic :
        (Set.prod (interior A) (interior B) : Set (X × Y)) ⊆ Set.prod A B := by
      intro q hq
      rcases hq with ⟨hqa, hqb⟩
      exact ⟨interior_subset hqa, interior_subset hqb⟩
    -- The rectangle is open
    have h_open : IsOpen (Set.prod (interior A) (interior B)) := by
      have h1 : IsOpen (interior A) := isOpen_interior
      have h2 : IsOpen (interior B) := isOpen_interior
      simpa using h1.prod h2
    -- Apply maximality of the interior
    exact interior_maximal h_basic h_open
  -- Monotonicity of closures
  have h_closure_subset :
      (closure (Set.prod (interior A) (interior B)) : Set (X × Y)) ⊆
        closure (interior (Set.prod A B)) :=
    closure_mono h_subset
  exact h_closure_subset hp_in_closure

theorem P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P2 A) : Topology.P2 (interior A) := by
  simpa using openSet_P2 (X := X) (A := interior A) isOpen_interior

theorem P1_and_P3_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (h1 : Topology.P1 A) (h3 : Topology.P3 A) : Topology.P2 A := by
  simpa using (P2_iff_P1_and_P3 (A := A)).2 ⟨h1, h3⟩

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P3 A) : Topology.P3 (interior A) := by
  dsimp [Topology.P3]
  intro x hx
  exact
    (interior_maximal
        (subset_closure : (interior A : Set X) ⊆ closure (interior A))
        isOpen_interior)
      hx

theorem P2_Union_countable {X : Type*} [TopologicalSpace X] {s : ℕ → Set X} (h : ∀ n, Topology.P2 (s n)) : Topology.P2 (⋃ n, s n) := by
  simpa using (P2_Union_family (X := X) (s := s) h)

theorem P2_sUnion_directed {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (hdir : DirectedOn (· ⊆ ·) 𝒜) (h : ∀ A ∈ 𝒜, Topology.P2 A) : Topology.P2 (⋃₀ 𝒜) := by
  simpa using
    (P2_sUnion_family (ι := Unit) (X := X) (𝒜 := 𝒜) h)

theorem P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P1 A) : Topology.P1 (closure A) := by
  dsimp [Topology.P1] at hA ⊢
  -- Establish the key inclusion `closure A ⊆ closure (interior (closure A))`
  have h_closure_subset :
      (closure A : Set X) ⊆ closure (interior (closure A)) := by
    -- First, `A ⊆ closure (interior (closure A))`
    have hA_subset : (A : Set X) ⊆ closure (interior (closure A)) := by
      -- From the hypothesis `A ⊆ closure (interior A)`
      have h1 : (A : Set X) ⊆ closure (interior A) := hA
      -- Monotonicity: `closure (interior A) ⊆ closure (interior (closure A))`
      have h2 : (closure (interior A) : Set X) ⊆
          closure (interior (closure A)) := by
        have h_sub : (interior A : Set X) ⊆ interior (closure A) :=
          interior_mono (subset_closure : (A : Set X) ⊆ closure A)
        exact closure_mono h_sub
      exact Set.Subset.trans h1 h2
    -- Since the right‐hand side is closed, it contains `closure A`
    exact closure_minimal hA_subset isClosed_closure
  -- Conclude the desired property
  intro x hx
  exact h_closure_subset hx

theorem P3_of_dense_closure {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Dense (closure A)) : Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hx
  -- `closure A` is the whole space thanks to density
  have h_closure_univ : (closure A : Set X) = (Set.univ : Set X) := by
    simpa [isClosed_closure.closure_eq] using hA.closure_eq
  -- hence its interior is also `univ`
  have h_interior_univ : (interior (closure A) : Set X) = Set.univ := by
    simpa [h_closure_univ, interior_univ]
  -- the inclusion is now obvious
  simpa [h_interior_univ]

theorem P2_exists_open_superset {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P2 A) : ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ U ⊆ interior (closure (interior A)) := by
  refine
    ⟨interior (closure (interior A)), isOpen_interior, hA, subset_rfl⟩

theorem interior_closure_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 (interior (closure A)) := by
  dsimp [Topology.P2]
  intro x hx
  -- `interior (closure A)` is open and contained in its closure, hence in the
  -- interior of that closure.
  have h_incl :
      (interior (closure A) : Set X) ⊆
        interior (closure (interior (closure A))) :=
    interior_maximal
      (subset_closure :
        (interior (closure A) : Set X) ⊆ closure (interior (closure A)))
      isOpen_interior
  have : x ∈ interior (closure (interior (closure A))) := h_incl hx
  simpa [interior_interior] using this

theorem P2_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : Topology.P2 A) (hB : Topology.P2 B) (hC : Topology.P2 C) : Topology.P2 (Set.prod A (Set.prod B C)) := by
  -- First, obtain `P2` for the product `B × C`.
  have hBC : Topology.P2 (Set.prod B C) := by
    simpa using (P2_prod (X := Y) (Y := Z) (A := B) (B := C) hB hC)
  -- Now, obtain `P2` for `A × (B × C)` using the previous result.
  simpa using
    (P2_prod (X := X) (Y := Y × Z) (A := A) (B := Set.prod B C) hA hBC)

theorem P1_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : Topology.P1 A) (hB : Topology.P1 B) (hC : Topology.P1 C) : Topology.P1 (Set.prod A (Set.prod B C)) := by
  -- First, obtain `P1` for the product `B × C`.
  have hBC : Topology.P1 (Set.prod B C) := by
    simpa using
      (P1_prod (X := Y) (Y := Z) (A := B) (B := C) hB hC)
  -- Now, obtain `P1` for `A × (B × C)` using the previous result.
  simpa using
    (P1_prod (X := X) (Y := Y × Z) (A := A) (B := Set.prod B C) hA hBC)

theorem P2_if_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure A = interior (closure (interior A))) : Topology.P2 A := by
  dsimp [Topology.P2]
  intro x hx
  have hx_closure : (x : X) ∈ closure A := subset_closure hx
  simpa [h] using hx_closure

theorem P1_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 (closure (interior A)) := by
  dsimp [Topology.P1]
  exact
    closure_mono
      (interior_maximal
        (subset_closure : (interior A : Set X) ⊆ closure (interior A))
        isOpen_interior)

theorem P3_closed_iff_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P3 A ↔ closure A = interior (closure A) := by
  simpa [hA.closure_eq] using (P3_closed_iff (X := X) (A := A) hA)

theorem P2_prod_four {W X Y Z : Type*} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set W} {B : Set X} {C : Set Y} {D : Set Z} (hA : Topology.P2 A) (hB : Topology.P2 B) (hC : Topology.P2 C) (hD : Topology.P2 D) : Topology.P2 (Set.prod (Set.prod A B) (Set.prod C D)) := by
  -- First, obtain `P2` for the product `A × B`.
  have hAB : Topology.P2 (Set.prod A B) :=
    P2_prod (X := W) (Y := X) (A := A) (B := B) hA hB
  -- Next, obtain `P2` for the product `C × D`.
  have hCD : Topology.P2 (Set.prod C D) :=
    P2_prod (X := Y) (Y := Z) (A := C) (B := D) hC hD
  -- Finally, apply the product lemma once more to get the desired result.
  simpa using
    (P2_prod (X := W × X) (Y := Y × Z)
      (A := Set.prod A B) (B := Set.prod C D) hAB hCD)

theorem P2_countable_Union {X : Type*} [TopologicalSpace X] {s : ℕ → Set X} (h : ∀ n, Topology.P2 (s n)) : Topology.P2 (⋃ n, interior (s n)) := by
  have h' : ∀ n, Topology.P2 (interior (s n)) := by
    intro n
    exact P2_interior (X := X) (A := s n) (h n)
  simpa using
    (P2_Union_countable (X := X) (s := fun n => interior (s n)) h')

theorem P3_prod_four {W X Y Z : Type*} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set W} {B : Set X} {C : Set Y} {D : Set Z} (hA : Topology.P3 A) (hB : Topology.P3 B) (hC : Topology.P3 C) (hD : Topology.P3 D) : Topology.P3 (Set.prod (Set.prod A B) (Set.prod C D)) := by
  -- First, obtain `P3` for the product `A × B`.
  have hAB : Topology.P3 (Set.prod A B) :=
    P3_prod (X := W) (Y := X) (A := A) (B := B) hA hB
  -- Next, obtain `P3` for the product `C × D`.
  have hCD : Topology.P3 (Set.prod C D) :=
    P3_prod (X := Y) (Y := Z) (A := C) (B := D) hC hD
  -- Finally, apply the product lemma once more to get the desired result.
  simpa using
    (P3_prod (X := W × X) (Y := Y × Z)
      (A := Set.prod A B) (B := Set.prod C D) hAB hCD)

theorem P3_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P3 (interior (closure A)) := by
  simpa using
    (openSet_P3 (X := X) (A := interior (closure A)) isOpen_interior)

theorem P1_of_closure_eq_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure A = interior A) : Topology.P1 A := by
  dsimp [P1]
  intro x hx
  -- first, `x` lies in `closure A`
  have hx_cl : x ∈ closure A := subset_closure hx
  -- rewrite using the equality `closure A = interior A`
  have hx_int : x ∈ interior A := by
    simpa [h] using hx_cl
  -- `interior A ⊆ closure (interior A)`
  exact subset_closure hx_int

theorem P2_iUnion_finite {X : Type*} [TopologicalSpace X] {s : Finset (Set X)} (h : ∀ A ∈ s, Topology.P2 A) : Topology.P2 (⋃ A ∈ s, A) := by
  classical
  -- Unfold the definition of `P2`
  dsimp [Topology.P2]
  -- Take a point of the big union
  intro x hxU
  /- 1.  Choose a particular set `A ∈ s` that contains `x`. -/
  rcases Set.mem_iUnion.1 hxU with ⟨A, hxU₁⟩
  rcases Set.mem_iUnion.1 hxU₁ with ⟨hA_mem, hxA⟩
  /- 2.  `A` itself satisfies `P2`. -/
  have hA_P2 : (A : Set X) ⊆ interior (closure (interior A)) :=
    h A hA_mem
  have hx₁ : x ∈ interior (closure (interior A)) := hA_P2 hxA
  /- 3.  Monotonicity:  
         `interior (closure (interior A)) ⊆
          interior (closure (interior ⋃ B ∈ s, B))`. -/
  -- First: `A ⊆ ⋃ B ∈ s, B`
  have hA_subset_union : (A : Set X) ⊆ ⋃ B ∈ s, B := by
    intro y hy
    -- Build the membership in the double `iUnion`
    apply Set.mem_iUnion.2
    refine ⟨A, ?_⟩
    apply Set.mem_iUnion.2
    exact ⟨hA_mem, hy⟩
  -- Hence `interior A ⊆ interior (⋃ B ∈ s, B)`
  have h_int_subset :
      (interior A : Set X) ⊆ interior (⋃ B ∈ s, B) :=
    interior_mono hA_subset_union
  -- Taking closures then interiors again
  have h_closure_subset :
      (closure (interior A) : Set X) ⊆
        closure (interior (⋃ B ∈ s, B)) :=
    closure_mono h_int_subset
  have h_interior_closure_subset :
      interior (closure (interior A)) ⊆
        interior (closure (interior (⋃ B ∈ s, B))) :=
    interior_mono h_closure_subset
  /- 4.  Finish. -/
  exact h_interior_closure_subset hx₁

theorem P2_iff_exists_open_between {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A ↔ ∃ U, IsOpen U ∧ A ⊆ U ∧ U ⊆ interior (closure (interior A)) := by
  constructor
  · intro hP2
    exact P2_exists_open_superset (A := A) hP2
  · rintro ⟨U, _hUopen, hAU, hUsubset⟩
    exact fun x hx => hUsubset (hAU hx)

theorem P3_of_closure_open {X : Type*} [TopologicalSpace X] {A : Set X} (h : IsOpen (closure A)) : Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hx
  have : (x : X) ∈ closure A := subset_closure hx
  simpa [h.interior_eq] using this

theorem P1_frontier_subset {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P1 A) : frontier A ⊆ closure (interior A) := by
  -- Take an arbitrary point of the frontier
  intro x hx
  -- From `P1` we know the two closures coincide
  have hEq : (closure A : Set X) = closure (interior A) := by
    simpa using
      (Eq.symm
        ((P1_iff_closure_interior_eq_closure (X := X) (A := A)).1 hA))
  -- `x` is in `closure A`, hence (using the equality) in `closure (interior A)`
  have hx_closureInt : x ∈ closure (interior A) := by
    have hx_closureA : x ∈ closure A := hx.1
    simpa [hEq] using hx_closureA
  exact hx_closureInt

theorem P1_superset_exists_open {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A → ∃ U, IsOpen U ∧ A ⊆ closure U := by
  intro hP1
  exact ⟨interior A, isOpen_interior, hP1⟩

theorem P1_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} (hA : Topology.P1 A) (hB : Topology.P1 B) (hC : Topology.P1 C) : Topology.P1 (A ∪ B ∪ C) := by
  have hBC : Topology.P1 (B ∪ C) := P1_union (X := X) hB hC
  have hABC : Topology.P1 (A ∪ (B ∪ C)) := P1_union (X := X) hA hBC
  simpa [Set.union_assoc] using hABC

theorem P2_if_P1_and_dense {X : Type*} [TopologicalSpace X] {A : Set X} (h1 : Topology.P1 A) (hDense : Dense A) : Topology.P2 A := by
  exact (P2_iff_P1_and_P3 (A := A)).2 ⟨h1, P3_of_dense (A := A) hDense⟩

theorem P3_iInter_decreasing {ι : Sort _} {X : Type*} [TopologicalSpace X] {s : ι → Set X} (hdec : ∀ i j, s j ⊆ s i) (h : ∀ i, Topology.P3 (s i)) : Topology.P3 (⋂ i, s i) := by
  classical
  by_cases hne : (Nonempty ι)
  · -- The index type is non–empty: pick an index `i₀`.
    rcases hne with ⟨i₀⟩
    -- First, identify the intersection with `s i₀`.
    have h_eq : (⋂ i, s i : Set X) = s i₀ := by
      apply Set.Subset.antisymm
      · intro x hx
        exact (Set.mem_iInter.1 hx) i₀
      · intro x hx
        have hx_all : ∀ j, x ∈ s j := by
          intro j
          have h_subset : (s i₀ : Set X) ⊆ s j := hdec j i₀
          exact h_subset hx
        exact (Set.mem_iInter.2 hx_all)
    -- Use the `P3` property for `s i₀` and rewrite using the equality above.
    have hP3_i0 : Topology.P3 (s i₀) := h i₀
    simpa [h_eq] using hP3_i0
  · -- The index type is empty: the intersection is the whole space.
    haveI : IsEmpty ι := ⟨fun i => (hne ⟨i⟩).elim⟩
    have h_eq_univ : (⋂ i, s i : Set X) = (Set.univ : Set X) := by
      ext x
      simp [Set.mem_iInter]
    simpa [h_eq_univ] using (P3_univ (X := X))

theorem P2_prod_five {V W X Y Z : Type*} [TopologicalSpace V] [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set V} {B : Set W} {C : Set X} {D : Set Y} {E : Set Z} (hA : Topology.P2 A) (hB : Topology.P2 B) (hC : Topology.P2 C) (hD : Topology.P2 D) (hE : Topology.P2 E) : Topology.P2 (Set.prod (Set.prod (Set.prod A B) C) (Set.prod D E)) := by
  -- `P2` for the first two factors `A × B`.
  have hAB : Topology.P2 (Set.prod A B) :=
    P2_prod (X := V) (Y := W) (A := A) (B := B) hA hB
  -- `P2` for the triple product `(A × B) × C`.
  have hABC : Topology.P2 (Set.prod (Set.prod A B) C) :=
    P2_prod (X := V × W) (Y := X) (A := Set.prod A B) (B := C) hAB hC
  -- `P2` for the last two factors `D × E`.
  have hDE : Topology.P2 (Set.prod D E) :=
    P2_prod (X := Y) (Y := Z) (A := D) (B := E) hD hE
  -- Combine the two products.
  simpa using
    (P2_prod (X := (V × W) × X) (Y := Y × Z)
      (A := Set.prod (Set.prod A B) C) (B := Set.prod D E) hABC hDE)

theorem P1_prod_five {V W X Y Z : Type*} [TopologicalSpace V] [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set V} {B : Set W} {C : Set X} {D : Set Y} {E : Set Z} (hA : Topology.P1 A) (hB : Topology.P1 B) (hC : Topology.P1 C) (hD : Topology.P1 D) (hE : Topology.P1 E) : Topology.P1 (Set.prod (Set.prod (Set.prod A B) C) (Set.prod D E)) := by
  -- First, obtain `P1` for the product `A × B`.
  have hAB : Topology.P1 (Set.prod A B) :=
    P1_prod (X := V) (Y := W) (A := A) (B := B) hA hB
  -- Next, obtain `P1` for the triple product `(A × B) × C`.
  have hABC : Topology.P1 (Set.prod (Set.prod A B) C) :=
    P1_prod (X := V × W) (Y := X) (A := Set.prod A B) (B := C) hAB hC
  -- `P1` for the product `D × E`.
  have hDE : Topology.P1 (Set.prod D E) :=
    P1_prod (X := Y) (Y := Z) (A := D) (B := E) hD hE
  -- Combine the two products.
  simpa using
    (P1_prod (X := (V × W) × X) (Y := Y × Z)
      (A := Set.prod (Set.prod A B) C) (B := Set.prod D E) hABC hDE)

theorem P3_of_closure_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure A = Set.univ) : Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hx
  simpa [h, interior_univ]

theorem P2_of_interior_closure_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X} (h : interior (closure (interior A)) = Set.univ) : Topology.P2 A := by
  dsimp [Topology.P2]
  intro x hx
  simpa [h] using (Set.mem_univ x)

theorem P3_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : Topology.P3 A) (hB : Topology.P3 B) (hC : Topology.P3 C) : Topology.P3 (Set.prod (Set.prod A B) C) := by
  -- First obtain `P3` for the product `A × B`.
  have hAB : Topology.P3 (Set.prod A B) :=
    P3_prod (X := X) (Y := Y) (A := A) (B := B) hA hB
  -- Then apply the two‐factor result once more.
  simpa using
    (P3_prod (X := X × Y) (Y := Z) (A := Set.prod A B) (B := C) hAB hC)

theorem P1_prod_four {W X Y Z : Type*} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set W} {B : Set X} {C : Set Y} {D : Set Z} (hA : Topology.P1 A) (hB : Topology.P1 B) (hC : Topology.P1 C) (hD : Topology.P1 D) : Topology.P1 (Set.prod (Set.prod A B) (Set.prod C D)) := by
  -- First, obtain `P1` for the product `A × B`.
  have hAB : Topology.P1 (Set.prod A B) :=
    P1_prod (X := W) (Y := X) (A := A) (B := B) hA hB
  -- Next, obtain `P1` for the product `C × D`.
  have hCD : Topology.P1 (Set.prod C D) :=
    P1_prod (X := Y) (Y := Z) (A := C) (B := D) hC hD
  -- Finally, combine the two products.
  simpa using
    (P1_prod (X := W × X) (Y := Y × Z)
      (A := Set.prod A B) (B := Set.prod C D) hAB hCD)

theorem P2_Union_monotone_nat {X : Type*} [TopologicalSpace X] {s : ℕ → Set X} (hmono : Monotone s) (h : ∀ n, Topology.P2 (s n)) : Topology.P2 (⋃ n, s n) := by
  simpa using (P2_Union_countable (X := X) (s := s) h)

theorem P3_iff_exists_open_subset {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P3 A ↔ ∃ U, IsOpen U ∧ U ⊆ closure A ∧ A ⊆ interior U := by
  -- First direction : `P3 A → ∃ U, ...`
  constructor
  · intro hP3
    -- Choose `U = interior (closure A)`
    refine
      ⟨interior (closure A), isOpen_interior, interior_subset, ?_⟩
    -- Since `U` is open, its interior is itself, hence
    -- `A ⊆ interior U` follows from `P3`.
    have h_eq : interior (interior (closure A)) = interior (closure A) := by
      simpa using interior_interior (closure A)
    simpa [h_eq] using hP3
  -- Second direction : the existence of an open `U` implies `P3 A`.
  · rintro ⟨U, hUopen, hU_subset, hA_subset⟩
    dsimp [Topology.P3] at *
    intro x hxA
    -- `x` belongs to `interior U`.
    have hx_intU : x ∈ interior U := hA_subset hxA
    -- Monotonicity of `interior` with `U ⊆ closure A`.
    have h_intU_to_intClA :
        (interior U : Set X) ⊆ interior (closure A) :=
      interior_mono hU_subset
    exact h_intU_to_intClA hx_intU

theorem P1_exists_closed_superset {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A → ∃ F : Set X, IsClosed F ∧ A ⊆ F ∧ F ⊆ closure (interior A) := by
  intro hP1
  exact ⟨closure (interior A), isClosed_closure, hP1, subset_rfl⟩

theorem P1_closure_union {X : Type*} [TopologicalSpace X] {A B : Set X} (h : Topology.P1 (closure (A ∪ B))) : Topology.P1 (closure A ∪ closure B) := by
  dsimp [Topology.P1] at h ⊢
  intro x hx
  -- View `x` as a point of `closure (A ∪ B)`
  have hx_cl : x ∈ closure (A ∪ B) := by
    simpa [closure_union] using hx
  -- Apply the hypothesis `h`
  have hx_in : x ∈ closure (interior (closure (A ∪ B))) := h hx_cl
  -- Rewrite back using `closure_union`
  simpa [closure_union] using hx_in

theorem P1_iff_closure_eq_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A ↔ closure A = closure (interior A) := by
  simpa [eq_comm] using
    (P1_iff_closure_interior_eq_closure (X := X) (A := A))

theorem P3_iUnion_finite {X : Type*} [TopologicalSpace X] {s : Finset (Set X)} (h : ∀ A ∈ s, Topology.P3 A) : Topology.P3 (⋃ A ∈ s, A) := by
  classical
  -- Unfold the definition of `P3`
  dsimp [Topology.P3]
  -- Take a point of the big union
  intro x hxU
  /- 1.  Choose a particular set `A ∈ s` that contains `x`. -/
  rcases Set.mem_iUnion.1 hxU with ⟨A, hxU₁⟩
  rcases Set.mem_iUnion.1 hxU₁ with ⟨hA_mem, hxA⟩
  /- 2.  `A` itself satisfies `P3`. -/
  have hA_P3 : (A : Set X) ⊆ interior (closure A) :=
    h A hA_mem
  have hx₁ : x ∈ interior (closure A) := hA_P3 hxA
  /- 3.  Monotonicity:  
         `interior (closure A) ⊆ interior (closure ⋃ B ∈ s, B)`. -/
  -- First: `A ⊆ ⋃ B ∈ s, B`
  have hA_subset_union : (A : Set X) ⊆ ⋃ B ∈ s, B := by
    intro y hy
    -- Build the membership in the double `iUnion`
    apply Set.mem_iUnion.2
    refine ⟨A, ?_⟩
    apply Set.mem_iUnion.2
    exact ⟨hA_mem, hy⟩
  -- Taking closures then interiors
  have h_closure_subset :
      (closure A : Set X) ⊆ closure (⋃ B ∈ s, B) :=
    closure_mono hA_subset_union
  have h_interior_closure_subset :
      interior (closure A) ⊆
        interior (closure (⋃ B ∈ s, B)) :=
    interior_mono h_closure_subset
  /- 4.  Finish. -/
  exact h_interior_closure_subset hx₁

theorem P2_of_open_neighborhoods {X : Type*} [TopologicalSpace X] {A : Set X} (h : ∀ x ∈ A, ∃ U, IsOpen U ∧ x ∈ U ∧ closure U ⊆ interior (closure (interior A))) : Topology.P2 A := by
  dsimp [Topology.P2]
  intro x hxA
  obtain ⟨U, _hUopen, hxU, hU_subset⟩ := h x hxA
  have hx_closure : (x : X) ∈ closure U := subset_closure hxU
  exact hU_subset hx_closure

theorem P1_iff_frontier_subset_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A ↔ frontier A ⊆ closure (interior A) := by
  classical
  constructor
  · intro hP1
    exact P1_frontier_subset (A := A) hP1
  · intro hFront
    dsimp [Topology.P1] at *
    intro x hxA
    by_cases hxInt : x ∈ interior A
    · -- `x` already lies in `interior A`
      exact subset_closure hxInt
    · -- `x` is not in `interior A`; hence it is on the frontier of `A`
      have hx_cl : x ∈ closure A := subset_closure hxA
      have hx_frontier : x ∈ frontier A := by
        -- `frontier A = closure A \ interior A`
        change x ∈ closure A \ interior A
        exact And.intro hx_cl hxInt
      exact hFront hx_frontier

theorem P2_prod_six {U V W X Y Z : Type*} [TopologicalSpace U] [TopologicalSpace V] [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set U} {B : Set V} {C : Set W} {D : Set X} {E : Set Y} {F : Set Z} (hA : Topology.P2 A) (hB : Topology.P2 B) (hC : Topology.P2 C) (hD : Topology.P2 D) (hE : Topology.P2 E) (hF : Topology.P2 F) : Topology.P2 (Set.prod (Set.prod (Set.prod A B) (Set.prod C D)) (Set.prod E F)) := by
  -- First, `P2` for the product `A × B`.
  have hAB : Topology.P2 (Set.prod A B) :=
    P2_prod (X := U) (Y := V) (A := A) (B := B) hA hB
  -- Next, `P2` for the product `C × D`.
  have hCD : Topology.P2 (Set.prod C D) :=
    P2_prod (X := W) (Y := X) (A := C) (B := D) hC hD
  -- Combine the two to obtain `P2` for `(A × B) × (C × D)`.
  have hABCD : Topology.P2 (Set.prod (Set.prod A B) (Set.prod C D)) :=
    P2_prod
      (X := U × V) (Y := W × X)
      (A := Set.prod A B) (B := Set.prod C D)
      hAB hCD
  -- `P2` for the product `E × F`.
  have hEF : Topology.P2 (Set.prod E F) :=
    P2_prod (X := Y) (Y := Z) (A := E) (B := F) hE hF
  -- Finally, combine once more to get the desired six–fold product.
  simpa using
    (P2_prod
      (X := (U × V) × (W × X))
      (Y := Y × Z)
      (A := Set.prod (Set.prod A B) (Set.prod C D))
      (B := Set.prod E F)
      hABCD
      hEF)

theorem P2_Union_monotone_nat_strong {X : Type*} [TopologicalSpace X] {s : ℕ → Set X} (hmono : Monotone s) (hP2 : ∀ n, Topology.P2 (s n)) : Topology.P2 (⋃ n, interior (s n)) := by
  simpa using (P2_countable_Union (X := X) (s := s) hP2)

theorem P1_closed_complement {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) (hP1 : Topology.P1 A) : Topology.P1 (Aᶜ) := by
  -- The complement of a closed set is open.
  have hOpen : IsOpen (Aᶜ : Set X) := hA.isOpen_compl
  -- Apply the lemma for open sets.
  simpa using (openSet_P1 (X := X) (A := Aᶜ) hOpen)

theorem P2_closed_complement {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) (hP2 : Topology.P2 A) : Topology.P2 (Aᶜ) := by
  have hOpen : IsOpen (Aᶜ : Set X) := hA.isOpen_compl
  simpa using (openSet_P2 (X := X) (A := Aᶜ) hOpen)

theorem P3_closed_complement {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) (hP3 : Topology.P3 A) : Topology.P3 (Aᶜ) := by
  have hOpen : IsOpen (Aᶜ : Set X) := hA.isOpen_compl
  simpa using (openSet_P3 (X := X) (A := Aᶜ) hOpen)

theorem P3_of_open_neighborhoods {X : Type*} [TopologicalSpace X] {A : Set X} (h : ∀ x ∈ A, ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ interior (closure A)) : Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hxA
  rcases h x hxA with ⟨U, _hUopen, hxU, hU_subset⟩
  exact hU_subset hxU

theorem P2_interior_subset {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P2 A) : interior A ⊆ interior (closure (interior A)) := by
  dsimp [Topology.P2] at h
  exact fun x hx => h (interior_subset hx)

theorem P1_of_open_surrounds {X : Type*} [TopologicalSpace X] {A : Set X} (h : ∀ x ∈ A, ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ closure (interior A)) : Topology.P1 A := by
  dsimp [Topology.P1]
  intro x hxA
  rcases h x hxA with ⟨U, _hUopen, hxU, hU_subset⟩
  exact hU_subset hxU

theorem P2_prod_symmetric {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : Topology.P2 (Set.prod A B) ↔ Topology.P2 (Set.prod B A) := by
  -- Let `e` be the swapping homeomorphism `(x, y) ↦ (y, x)`.
  let e := Homeomorph.prodComm X Y
  -- The image of `A × B` under `e` is `B × A`.
  have h_img :
      (e '' (Set.prod A B) : Set (Y × X)) = Set.prod B A := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases hq with ⟨hA, hB⟩
      exact And.intro hB hA
    · rintro hp
      rcases p with ⟨b, a⟩
      rcases hp with ⟨hB, hA⟩
      refine ⟨(a, b), ?_, ?_⟩
      · exact And.intro hA hB
      · rfl
  -- The image of `B × A` under the inverse map is `A × B`.
  have h_img_symm :
      (e.symm '' (Set.prod B A) : Set (X × Y)) = Set.prod A B := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases hq with ⟨hB, hA⟩
      exact And.intro hA hB
    · rintro hp
      rcases p with ⟨a, b⟩
      rcases hp with ⟨hA, hB⟩
      refine ⟨(b, a), ?_, ?_⟩
      · exact And.intro hB hA
      · rfl
  -- Use the two transport lemmas for `P2`.
  constructor
  · intro hP2
    -- Transport through `e`.
    have h :=
      P2_image_homeomorph
        (e := e)
        (A := Set.prod A B)
        hP2
    simpa [h_img] using h
  · intro hP2
    -- Transport back through `e.symm`.
    have h :=
      P2_image_homeomorph
        (e := e.symm)
        (A := Set.prod B A)
        hP2
    simpa [h_img_symm] using h

theorem P1_closure_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (h : ∀ A ∈ 𝒜, Topology.P1 A) : Topology.P1 (closure (⋃₀ 𝒜)) := by
  have hP1_union : Topology.P1 (⋃₀ 𝒜) :=
    P1_sUnion_family (X := X) (𝒜 := 𝒜) h
  simpa using
    (P1_closure (X := X) (A := ⋃₀ 𝒜) hP1_union)

theorem P2_closed_complement' {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P2 (Aᶜ) := by
  have hOpen : IsOpen (Aᶜ : Set X) := hA.isOpen_compl
  simpa using (openSet_P2 (X := X) (A := Aᶜ) hOpen)

theorem P3_interior_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : Topology.P3 (Set.prod (interior A) (interior B)) := by
  -- First, observe that the product of two open sets is open.
  have hOpen : IsOpen (Set.prod (interior A) (interior B)) := by
    exact
      (isOpen_interior : IsOpen (interior A)).prod
        (isOpen_interior : IsOpen (interior B))
  -- Apply the `P3` lemma for open sets in the ambient space `X × Y`.
  simpa using
    (openSet_P3 (X := X × Y)
      (A := Set.prod (interior A) (interior B)) hOpen)

theorem P2_exists_basis {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A → ∃ 𝔅 : Set (Set X), (∀ U ∈ 𝔅, IsOpen U) ∧ A ⊆ ⋃₀ 𝔅 ∧ ⋃₀ 𝔅 ⊆ interior (closure (interior A)) := by
  intro hP2
  refine ⟨{interior (closure (interior A))}, ?_, ?_, ?_⟩
  · intro U hU
    have hUeq : U = interior (closure (interior A)) := by
      simpa [Set.mem_singleton_iff] using hU
    simpa [hUeq] using isOpen_interior
  · simpa [Set.sUnion_singleton] using hP2
  ·
    simpa [Set.sUnion_singleton] using
      (subset_rfl :
        (interior (closure (interior A)) : Set X) ⊆
          interior (closure (interior A)))

theorem P1_subsingleton_space {X : Type*} [TopologicalSpace X] [Subsingleton X] (A : Set X) : Topology.P1 A := by
  classical
  by_cases hAempty : (A : Set X) = ∅
  · -- Empty set case
    simpa [hAempty] using (P1_empty (X := X))
  · -- Non-empty case: in a subsingleton space this forces `A = univ`
    have hAuniv : (A : Set X) = (Set.univ : Set X) := by
      -- Pick an element of `A`
      obtain ⟨a, ha⟩ :=
        (Set.nonempty_iff_ne_empty).2 hAempty
      -- Show every element belongs to `A`
      ext x
      constructor
      · intro hx
        trivial
      · intro _
        -- All points are equal in a subsingleton space
        have : x = a := Subsingleton.elim _ _
        simpa [this] using ha
    -- Apply the `univ` lemma
    simpa [hAuniv] using (P1_univ (X := X))

theorem P2_iUnion_increasing {ι : Sort _} {X : Type*} [TopologicalSpace X] {s : ι → Set X} (hmono : ∀ i j, s i ⊆ s j) (h : ∀ i, Topology.P2 (s i)) : Topology.P2 (⋃ i, s i) := by
  simpa using (P2_Union_family (X := X) (s := s) h)

theorem P1_iInter_decreasing {ι : Sort _} {X : Type*} [TopologicalSpace X] {s : ι → Set X} (hdec : ∀ i j, s j ⊆ s i) (h : ∀ i, Topology.P1 (s i)) : Topology.P1 (⋂ i, s i) := by
  classical
  by_cases hne : (Nonempty ι)
  · -- The index type is inhabited: pick an index `i₀`.
    rcases hne with ⟨i₀⟩
    -- First, identify the intersection with `s i₀`.
    have h_eq : (⋂ i, s i : Set X) = s i₀ := by
      apply Set.Subset.antisymm
      · intro x hx
        exact (Set.mem_iInter.1 hx) i₀
      · intro x hx
        have hx_all : ∀ j, x ∈ s j := by
          intro j
          have h_subset : (s i₀ : Set X) ⊆ s j := hdec j i₀
          exact h_subset hx
        exact (Set.mem_iInter.2 hx_all)
    -- Apply `P1` to `s i₀` and rewrite using the equality above.
    have hP1_i0 : Topology.P1 (s i₀) := h i₀
    simpa [h_eq] using hP1_i0
  · -- The index type is empty: the intersection is `univ`.
    haveI : IsEmpty ι := ⟨fun i => (hne ⟨i⟩).elim⟩
    have h_eq_univ : (⋂ i, s i : Set X) = (Set.univ : Set X) := by
      ext x
      simp [Set.mem_iInter]
    simpa [h_eq_univ] using (P1_univ (X := X))

theorem P2_iInter_decreasing {ι : Sort _} {X : Type*} [TopologicalSpace X] {s : ι → Set X} (hdec : ∀ i j, s j ⊆ s i) (h : ∀ i, Topology.P2 (s i)) : Topology.P2 (⋂ i, s i) := by
  -- First, obtain `P1` for the intersection using the decreasing property.
  have hP1 : Topology.P1 (⋂ i, s i) :=
    P1_iInter_decreasing (s := s) hdec
      (fun i => P2_implies_P1 (A := s i) (h i))
  -- Next, obtain `P3` for the intersection in the same way.
  have hP3 : Topology.P3 (⋂ i, s i) :=
    P3_iInter_decreasing (s := s) hdec
      (fun i => P2_implies_P3 (A := s i) (h i))
  -- Combine the two properties to get `P2`.
  simpa using
    (P2_iff_P1_and_P3 (A := ⋂ i, s i)).2 ⟨hP1, hP3⟩

theorem P1_prod_symmetric {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : Topology.P1 (Set.prod A B) ↔ Topology.P1 (Set.prod B A) := by
  -- Define the swapping homeomorphism
  let e := Homeomorph.prodComm X Y
  -- Characterise its action on the rectangle `A × B`.
  have h_img :
      (e '' (Set.prod A B) : Set (Y × X)) = Set.prod B A := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases hq with ⟨hA, hB⟩
      exact And.intro hB hA
    · rintro hp
      rcases p with ⟨b, a⟩
      rcases hp with ⟨hB, hA⟩
      refine ⟨(a, b), ?_, ?_⟩
      · exact And.intro hA hB
      · rfl
  -- And similarly for the inverse map.
  have h_img_symm :
      (e.symm '' (Set.prod B A) : Set (X × Y)) = Set.prod A B := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases hq with ⟨hB, hA⟩
      exact And.intro hA hB
    · rintro hp
      rcases p with ⟨a, b⟩
      rcases hp with ⟨hA, hB⟩
      refine ⟨(b, a), ?_, ?_⟩
      · exact And.intro hB hA
      · rfl
  -- Transfer the property through the homeomorphism and its inverse.
  constructor
  · intro hP1
    have h := P1_image_homeomorph (e := e) (A := Set.prod A B) hP1
    simpa [h_img] using h
  · intro hP1
    have h := P1_image_homeomorph (e := e.symm) (A := Set.prod B A) hP1
    simpa [h_img_symm] using h

theorem P3_prod_symmetric {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : Topology.P3 (Set.prod A B) ↔ Topology.P3 (Set.prod B A) := by
  -- Swapping homeomorphism
  let e := Homeomorph.prodComm X Y
  -- Image of `A × B` under `e`
  have h_img :
      (e '' Set.prod A B : Set (Y × X)) = Set.prod B A := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases hq with ⟨hA, hB⟩
      exact And.intro hB hA
    · rintro hp
      rcases p with ⟨b, a⟩
      rcases hp with ⟨hB, hA⟩
      refine ⟨(a, b), ?_, ?_⟩
      · exact And.intro hA hB
      · rfl
  -- Image of `B × A` under `e.symm`
  have h_img_symm :
      (e.symm '' Set.prod B A : Set (X × Y)) = Set.prod A B := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases hq with ⟨hB, hA⟩
      exact And.intro hA hB
    · rintro hp
      rcases p with ⟨a, b⟩
      rcases hp with ⟨hA, hB⟩
      refine ⟨(b, a), ?_, ?_⟩
      · exact And.intro hB hA
      · rfl
  -- Transfer the `P3` property through the homeomorphism.
  constructor
  · intro hP3
    have h :=
      P3_image_homeomorph
        (e := e) (A := Set.prod A B) hP3
    simpa [h_img] using h
  · intro hP3
    have h :=
      P3_image_homeomorph
        (e := e.symm) (A := Set.prod B A) hP3
    simpa [h_img_symm] using h

theorem P2_subsingleton_space {X : Type*} [TopologicalSpace X] [Subsingleton X] (A : Set X) : Topology.P2 A := by
  classical
  by_cases hA : (A : Set X) = ∅
  · -- Empty set case
    simpa [hA] using (P2_empty (X := X))
  · -- Non-empty case: in a subsingleton space this forces `A = univ`
    have hAuniv : (A : Set X) = (Set.univ : Set X) := by
      -- Pick an element of `A`
      obtain ⟨a, ha⟩ := (Set.nonempty_iff_ne_empty).2 hA
      -- Show that every element belongs to `A`
      ext x
      constructor
      · intro _; trivial
      · intro _
        have : x = a := Subsingleton.elim _ _
        simpa [this] using ha
    -- Conclude using the fact that `univ` satisfies `P2`
    simpa [hAuniv] using (P2_univ (X := X))

theorem P3_subsingleton_space {X : Type*} [TopologicalSpace X] [Subsingleton X] (A : Set X) : Topology.P3 A := by
  classical
  by_cases hA : (A : Set X) = ∅
  · simpa [hA] using (P3_empty (X := X))
  ·
    -- In a non‐empty set of a subsingleton space we actually have `A = univ`.
    have hAuniv : (A : Set X) = (Set.univ : Set X) := by
      -- Pick an element of `A`.
      obtain ⟨a, ha⟩ := (Set.nonempty_iff_ne_empty).2 hA
      ext x
      constructor
      · intro _; trivial
      · intro _
        -- All points are equal in a subsingleton space.
        have : x = a := Subsingleton.elim _ _
        simpa [this] using ha
    -- Conclude using the fact that `univ` satisfies `P3`.
    simpa [hAuniv] using (P3_univ (X := X))

theorem P3_diff_closed {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P3 A) (hB : IsClosed B) : Topology.P3 (A \ B) := by
  -- Unfold the definition of `P3`
  dsimp [Topology.P3] at hA ⊢
  intro x hx
  -- `hx` splits into membership of `A` and non–membership of `B`
  have hxA : x ∈ A := hx.1
  have hxNotB : x ∈ Bᶜ := by
    simpa using hx.2
  -- From `P3 A` we get that `x` lies in `interior (closure A)`
  have hx_int_clA : x ∈ interior (closure A) := hA hxA
  ------------------------------------------------------------------
  -- An auxiliary open neighbourhood avoiding `B`
  ------------------------------------------------------------------
  set U : Set X := interior (closure A) ∩ Bᶜ with hU_def
  have hU_open : IsOpen U :=
    (isOpen_interior : IsOpen (interior (closure A))).inter hB.isOpen_compl
  have hxU : x ∈ U := by
    simpa [hU_def] using And.intro hx_int_clA hxNotB
  ------------------------------------------------------------------
  -- Show that `U` is contained in `closure (A \ B)`
  ------------------------------------------------------------------
  have hU_subset : (U : Set X) ⊆ closure (A \ B) := by
    intro y hy
    have hy_int_clA : y ∈ interior (closure A) := hy.1
    have hyNotB : y ∈ Bᶜ := hy.2
    have hy_clA : y ∈ closure A := interior_subset hy_int_clA
    -- Prove that `y` belongs to the closure of `A \ B`
    have : y ∈ closure (A \ B) := by
      -- Use the neighbourhood characterisation of the closure
      apply (mem_closure_iff).2
      intro V hVopen hyV
      -- Intersect the neighbourhood with `Bᶜ` (still open & contains `y`)
      have hWopen : IsOpen (V ∩ Bᶜ) := hVopen.inter hB.isOpen_compl
      have hyW : y ∈ V ∩ Bᶜ := And.intro hyV hyNotB
      -- Since `y ∈ closure A`, this intersection meets `A`
      have h_nonempty :=
        (mem_closure_iff).1 hy_clA (V ∩ Bᶜ) hWopen hyW
      rcases h_nonempty with ⟨z, hz⟩
      rcases hz with ⟨hzVB, hzA⟩
      rcases hzVB with ⟨hzV, hzNotB⟩
      -- The witness lies in `A \ B` and in `V`
      exact ⟨z, And.intro hzV ⟨hzA, hzNotB⟩⟩
    exact this
  ------------------------------------------------------------------
  -- Maximality of the interior gives the desired conclusion
  ------------------------------------------------------------------
  have : x ∈ interior (closure (A \ B)) :=
    (interior_maximal hU_subset hU_open) (by
      simpa [hU_def] using hxU)
  exact this

theorem P3_interior_compl {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P3 A) : Topology.P3 (interior Aᶜ) := by
  simpa using
    (openSet_P3 (X := X) (A := interior (Aᶜ)) isOpen_interior)

theorem P1_prod_interior {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : Topology.P1 (Set.prod (interior A) (interior B)) := by
  simpa using
    (openSet_P1
        (X := X × Y)
        (A := Set.prod (interior A) (interior B))
        ((isOpen_interior : IsOpen (interior A)).prod
          (isOpen_interior : IsOpen (interior B))))

theorem P1_closure_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P1 A) (hB : Topology.P1 B) : Topology.P1 (closure (Set.prod A B)) := by
  -- First, get `P1` for the product `A × B`.
  have hProd : Topology.P1 (Set.prod A B) :=
    P1_prod (X := X) (Y := Y) (A := A) (B := B) hA hB
  -- Then, take the closure of the product.
  simpa using
    (P1_closure (X := X × Y) (A := Set.prod A B) hProd)