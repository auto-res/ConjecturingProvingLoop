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


theorem P3_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : P3 A := by
  intro x hx
  exact (interior_mono (closure_mono interior_subset)) (hA hx)

theorem P1_univ {X : Type*} [TopologicalSpace X] : P1 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P2_empty {X : Type*} [TopologicalSpace X] : P2 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P3 A) (hB : P3 B) : P3 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hAx =>
      exact (interior_mono (closure_mono (Set.subset_union_left))) (hA hAx)
  | inr hBx =>
      exact (interior_mono (closure_mono (Set.subset_union_right))) (hB hBx)

theorem P1_empty {X : Type*} [TopologicalSpace X] : P1 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P3_empty {X : Type*} [TopologicalSpace X] : P3 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P1_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : P1 A := by
  intro x hx
  exact interior_subset (hA hx)

theorem P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A := by
  intro x hx
  have hsubset : (A : Set X) ⊆ interior (closure A) :=
    interior_maximal (subset_closure) hA
  simpa [hA.interior_eq] using hsubset hx

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P2 A) (hB : P2 B) : P2 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hAx =>
      have hsubset :
        interior (closure (interior A)) ⊆
          interior (closure (interior (A ∪ B))) :=
        interior_mono
          (closure_mono
            (interior_mono
              (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)))
      exact hsubset (hA hAx)
  | inr hBx =>
      have hsubset :
        interior (closure (interior B)) ⊆
          interior (closure (interior (A ∪ B))) :=
        interior_mono
          (closure_mono
            (interior_mono
              (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)))
      exact hsubset (hB hBx)

theorem P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (interior A) := by
  intro x hx
  simpa [interior_interior] using (subset_closure hx)

theorem P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P2 (interior A) := by
  intro x hx
  -- First, show the needed set inclusion.
  have hsubset : (interior A : Set X) ⊆ interior (closure (interior A)) := by
    -- `interior (interior A)` is contained in `interior (closure (interior A))`.
    have h : interior (interior A) ⊆ interior (closure (interior A)) :=
      interior_mono (subset_closure : (interior A : Set X) ⊆ closure (interior A))
    simpa [interior_interior] using h
  -- Apply the inclusion to the given point.
  have : x ∈ interior (closure (interior A)) := hsubset hx
  -- Rewrite the goal and finish.
  simpa [interior_interior] using this

theorem P1_iff_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ closure (interior A) = closure A := by
  -- Unfold the definition of `P1`.
  unfold P1
  constructor
  · intro hA
    -- `closure (interior A)` is contained in `closure A`.
    have h₁ : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    -- Taking closures of the hypothesis gives the reverse inclusion.
    have h₂ : closure A ⊆ closure (interior A) := by
      have : closure A ⊆ closure (closure (interior A)) := closure_mono hA
      simpa [closure_closure] using this
    exact subset_antisymm h₁ h₂
  · intro h_eq
    intro x hx
    -- Every point of `A` lies in `closure A`, which equals `closure (interior A)`.
    have : x ∈ closure A := subset_closure hx
    simpa [h_eq] using this

theorem P2_iff_P1_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A ↔ P1 A := by
  constructor
  · intro h
    exact P1_of_P2 h
  · intro _
    exact P2_of_open hA

theorem P2_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort _} {s : ι → Set X} (h : ∀ i, P2 (s i)) : P2 (⋃ i, s i) := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
  have hx₁ : x ∈ interior (closure (interior (s i))) := (h i) hxi
  have hsubset :
      interior (closure (interior (s i))) ⊆
        interior (closure (interior (⋃ j, s j))) := by
    exact
      interior_mono
        (closure_mono
          (interior_mono
            (Set.subset_iUnion _ i)))
  exact hsubset hx₁

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {S : Set (Set X)} (h : ∀ A ∈ S, P1 A) : P1 (⋃₀ S) := by
  intro x hx
  rcases Set.mem_sUnion.mp hx with ⟨A, hAS, hxA⟩
  have hP1 : P1 A := h A hAS
  have hx_cl : x ∈ closure (interior A) := hP1 hxA
  -- Show that `interior A ⊆ interior (⋃₀ S)`.
  have hsub : (interior A : Set X) ⊆ interior (⋃₀ S) := by
    -- First, `interior A ⊆ ⋃₀ S`.
    have hsub0 : (interior A : Set X) ⊆ ⋃₀ S := by
      intro y hy
      have hyA : y ∈ A := interior_subset hy
      exact Set.mem_sUnion.mpr ⟨A, hAS, hyA⟩
    -- Then take interiors on both sides.
    have hsub1 : interior (interior A) ⊆ interior (⋃₀ S) :=
      interior_mono hsub0
    simpa [interior_interior] using hsub1
  -- Take closures to obtain the desired inclusion.
  have hsubset_cl :
      closure (interior A) ⊆ closure (interior (⋃₀ S)) :=
    closure_mono hsub
  exact hsubset_cl hx_cl

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Dense A) : P3 A := by
  intro x hx
  simpa [hA.closure_eq, interior_univ]

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P1 A) (hB : P1 B) : P1 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hAx =>
      have hsubset :
          closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono
          (interior_mono
            (Set.subset_union_left : (A : Set X) ⊆ A ∪ B))
      exact hsubset (hA hAx)
  | inr hBx =>
      have hsubset :
          closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono
          (interior_mono
            (Set.subset_union_right : (B : Set X) ⊆ A ∪ B))
      exact hsubset (hB hBx)

theorem P1_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort _} {s : ι → Set X} (h : ∀ i, P1 (s i)) : P1 (⋃ i, s i) := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
  have hx_cl : x ∈ closure (interior (s i)) := (h i) hxi
  have hsubset :
      closure (interior (s i)) ⊆
        closure (interior (⋃ j, s j)) := by
    exact
      closure_mono
        (interior_mono
          (Set.subset_iUnion _ i))
  exact hsubset hx_cl

theorem P3_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort _} {s : ι → Set X} (h : ∀ i, P3 (s i)) : P3 (⋃ i, s i) := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
  have hx₁ : x ∈ interior (closure (s i)) := (h i) hxi
  have hsubset :
      interior (closure (s i)) ⊆
        interior (closure (⋃ j, s j)) := by
    exact
      interior_mono
        (closure_mono
          (Set.subset_iUnion _ i))
  exact hsubset hx₁

theorem P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P3 A := by
  intro x hx
  have hx_int : x ∈ interior A := by
    simpa [hA.interior_eq] using hx
  have hsubset : (interior A : Set X) ⊆ interior (closure A) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  exact hsubset hx_int

theorem P1_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P1 A := by
  intro x hx
  simpa [hA.interior_eq] using (subset_closure hx)

theorem P3_iff_P2_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P3 A ↔ P2 A := by
  -- Useful rewrites and inclusions stemming from `hA`
  have h_closure_eq : closure A = A := hA.closure_eq
  have h_int_eq : interior (closure A) = interior A := by
    simpa [h_closure_eq]
  have h_closure_subset : closure (interior A) ⊆ A := by
    have : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : (interior A : Set X) ⊆ A)
    simpa [h_closure_eq] using this
  have h_int_subset : interior (closure (interior A)) ⊆ interior A :=
    interior_mono h_closure_subset
  have h_subset_int : interior A ⊆ interior (closure (interior A)) := by
    have h_sub : (interior A : Set X) ⊆ closure (interior A) := subset_closure
    exact interior_maximal h_sub isOpen_interior
  -- Now prove the equivalence
  constructor
  · intro hP3
    intro x hx
    -- From `P3` we enter `interior A`
    have hx_intA : x ∈ interior A := by
      have h := hP3 hx
      simpa [h_int_eq] using h
    -- Expand to the larger interior required by `P2`
    exact h_subset_int hx_intA
  · intro hP2
    intro x hx
    -- `hP2` gives the larger interior; shrink it to `interior A`
    have hx_intA : x ∈ interior A := h_int_subset (hP2 hx)
    -- Rewrite back to `interior (closure A)` for `P3`
    simpa [h_int_eq] using hx_intA

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {S : Set (Set X)} (h : ∀ A ∈ S, P3 A) : P3 (⋃₀ S) := by
  intro x hx
  rcases Set.mem_sUnion.mp hx with ⟨A, hAS, hxA⟩
  have hP3A : P3 A := h A hAS
  have hx_int_clA : x ∈ interior (closure A) := hP3A hxA
  have hsubset :
      interior (closure A) ⊆ interior (closure (⋃₀ S)) := by
    have hsub : (A : Set X) ⊆ ⋃₀ S := by
      intro y hy
      exact Set.mem_sUnion.mpr ⟨A, hAS, hy⟩
    exact interior_mono (closure_mono hsub)
  exact hsubset hx_int_clA

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {S : Set (Set X)} (h : ∀ A ∈ S, P2 A) : P2 (⋃₀ S) := by
  intro x hx
  rcases Set.mem_sUnion.mp hx with ⟨A, hAS, hxA⟩
  have hP2A : P2 A := h A hAS
  have hx_int : x ∈ interior (closure (interior A)) := hP2A hxA
  -- We will prove that `interior (closure (interior A))` is contained in
  -- `interior (closure (interior (⋃₀ S)))`.
  -- First, note that `interior A ⊆ ⋃₀ S`.
  have hsub0 : (interior A : Set X) ⊆ ⋃₀ S := by
    intro y hy
    have hyA : y ∈ A := interior_subset hy
    exact Set.mem_sUnion.mpr ⟨A, hAS, hyA⟩
  -- Hence `interior A ⊆ interior (⋃₀ S)`.
  have hsub_int : (interior A : Set X) ⊆ interior (⋃₀ S) := by
    simpa [interior_interior] using (interior_mono hsub0)
  -- Taking closures and then interiors gives the desired inclusion.
  have hsubset :
      interior (closure (interior A)) ⊆
        interior (closure (interior (⋃₀ S))) := by
    exact
      interior_mono
        (closure_mono hsub_int)
  exact hsubset hx_int

theorem P2_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] (A : Set X) : P2 A := by
  intro x hx
  -- First, show that `A` must be the whole space.
  have hA_univ : (A : Set X) = Set.univ := by
    ext y
    constructor
    · intro _; simp
    · intro _
      have h_eq : y = x := Subsingleton.elim _ _
      simpa [h_eq] using hx
  -- Now the claim follows by rewriting with `hA_univ`.
  simpa [hA_univ, interior_univ, closure_univ]

theorem P3_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} (hA : P3 A) (hB : P3 B) (hC : P3 C) : P3 (A ∪ B ∪ C) := by
  -- Combine `A` and `B`
  have hAB : P3 (A ∪ B) := P3_union hA hB
  -- Combine the previous union with `C`
  have hABC : P3 ((A ∪ B) ∪ C) := P3_union hAB hC
  simpa [Set.union_assoc] using hABC

theorem P2_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} : P2 A ↔ P2 (e '' A) := by
  classical
  constructor
  · intro hP2
    intro y hy
    rcases hy with ⟨x, hxA, rfl⟩
    have hx : x ∈ interior (closure (interior A)) := hP2 hxA
    -- step 1 : transport through `e`
    have hx₁ : e x ∈ e '' interior (closure (interior A)) := ⟨x, hx, rfl⟩
    -- step 2 : rewrite with `image_interior`
    have hx₂ : e x ∈ interior (e '' closure (interior A)) := by
      simpa [e.image_interior (s := closure (interior A))] using hx₁
    -- step 3 : rewrite with `image_closure`
    have hx₃ : e x ∈ interior (closure (e '' interior A)) := by
      simpa [e.image_closure (s := interior A)] using hx₂
    -- step 4 : rewrite once more with `image_interior`
    have hx₄ : e x ∈ interior (closure (interior (e '' A))) := by
      simpa [e.image_interior (s := A)] using hx₃
    exact hx₄
  · intro hP2'
    intro x hxA
    -- image point
    have hy : e x ∈ e '' A := ⟨x, hxA, rfl⟩
    -- apply hypothesis on the image
    have hy' : e x ∈ interior (closure (interior (e '' A))) := hP2' hy
    -- transport back with `e.symm`
    have hx₁ : x ∈ e.symm '' interior (closure (interior (e '' A))) := by
      exact ⟨e x, hy', by simp⟩
    -- use `image_interior` for `e.symm`
    have hx₂ : x ∈ interior (e.symm '' closure (interior (e '' A))) := by
      simpa [e.symm.image_interior (s := closure (interior (e '' A)))] using hx₁
    -- use `image_closure` for `e.symm`
    have hx₃ : x ∈ interior (closure (e.symm '' interior (e '' A))) := by
      simpa [e.symm.image_closure (s := interior (e '' A))] using hx₂
    -- identify `e.symm '' interior (e '' A)` with `interior A`
    -- first, raw images
    have h_image : e.symm '' (e '' A) = (A : Set X) := by
      ext z
      constructor
      · intro hz
        rcases hz with ⟨y, ⟨x', hx'A, rfl⟩, hzy⟩
        have h_eq : x' = z := by
          have : e.symm (e x') = z := by
            simpa using hzy
          simpa [e.symm_apply_apply] using this
        simpa [h_eq] using hx'A
      · intro hz
        exact ⟨e z, ⟨z, hz, rfl⟩, by simp⟩
    have hint : e.symm '' interior (e '' A) = interior A := by
      have h := e.symm.image_interior (s := e '' A)
      simpa [h_image] using h
    have hx_final : x ∈ interior (closure (interior A)) := by
      simpa [hint] using hx₃
    exact hx_final

theorem P3_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} : P3 A ↔ P3 (e '' A) := by
  classical
  constructor
  · intro hP3
    intro y hy
    rcases hy with ⟨x, hxA, rfl⟩
    have hx : x ∈ interior (closure A) := hP3 hxA
    have hx₁ : e x ∈ e '' interior (closure A) := ⟨x, hx, rfl⟩
    have hx₂ : e x ∈ interior (e '' closure A) := by
      simpa [e.image_interior (s := closure A)] using hx₁
    have hx₃ : e x ∈ interior (closure (e '' A)) := by
      simpa [e.image_closure (s := A)] using hx₂
    exact hx₃
  · intro hP3'
    intro x hxA
    have hy : e x ∈ e '' A := ⟨x, hxA, rfl⟩
    have hy' : e x ∈ interior (closure (e '' A)) := hP3' hy
    have hx₁ : x ∈ e.symm '' interior (closure (e '' A)) := by
      exact ⟨e x, hy', by simp⟩
    have hx₂ : x ∈ interior (e.symm '' closure (e '' A)) := by
      simpa [e.symm.image_interior (s := closure (e '' A))] using hx₁
    have hx₃ : x ∈ interior (closure (e.symm '' (e '' A))) := by
      simpa [e.symm.image_closure (s := e '' A)] using hx₂
    have h_image : e.symm '' (e '' A) = (A : Set X) := by
      ext z
      constructor
      · intro hz
        rcases hz with ⟨y, ⟨x', hx'A, rfl⟩, hzy⟩
        have h_eq : x' = z := by
          have : e.symm (e x') = z := by
            simpa using hzy
          simpa [e.symm_apply_apply] using this
        simpa [h_eq] using hx'A
      · intro hz
        exact ⟨e z, ⟨z, hz, rfl⟩, by simp⟩
    simpa [h_image] using hx₃

theorem P1_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} : P1 A ↔ P1 (e '' A) := by
  classical
  constructor
  · intro hP1
    intro y hy
    rcases hy with ⟨x, hxA, rfl⟩
    have hx : x ∈ closure (interior A) := hP1 hxA
    have hx₁ : e x ∈ e '' closure (interior A) := ⟨x, hx, rfl⟩
    have hx₂ : e x ∈ closure (e '' interior A) := by
      simpa [e.image_closure (s := interior A)] using hx₁
    have hx₃ : e x ∈ closure (interior (e '' A)) := by
      simpa [e.image_interior (s := A)] using hx₂
    exact hx₃
  · intro hP1'
    intro x hxA
    have hy : e x ∈ e '' A := ⟨x, hxA, rfl⟩
    have hy' : e x ∈ closure (interior (e '' A)) := hP1' hy
    have hx₁ : x ∈ e.symm '' closure (interior (e '' A)) := ⟨e x, hy', by simp⟩
    have hx₂ : x ∈ closure (e.symm '' interior (e '' A)) := by
      simpa [e.symm.image_closure (s := interior (e '' A))] using hx₁
    have h_image : e.symm '' (e '' A) = (A : Set X) := by
      ext z
      constructor
      · intro hz
        rcases hz with ⟨y, ⟨x', hx'A, rfl⟩, hzy⟩
        have : x' = z := by
          have : e.symm (e x') = z := by
            simpa using hzy
          simpa [e.symm_apply_apply] using this
        simpa [this] using hx'A
      · intro hz
        exact ⟨e z, ⟨z, hz, rfl⟩, by simp⟩
    have hint : e.symm '' interior (e '' A) = interior A := by
      have h := e.symm.image_interior (s := e '' A)
      simpa [h_image] using h
    have hx_final : x ∈ closure (interior A) := by
      simpa [hint] using hx₂
    exact hx_final

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P3 (interior A) := by
  exact P3_of_P2 (A := interior A) P2_interior

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense (interior A)) : P2 A := by
  intro x hx
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [h.closure_eq, interior_univ] using this

theorem P2_iff_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A ↔ P3 A := by
  constructor
  · intro hP2
    exact P3_of_P2 hP2
  · intro _
    exact P2_of_open hA

theorem P2_compl_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P2 (Aᶜ) := by
  simpa using (P2_of_open (A := Aᶜ) hA.isOpen_compl)

theorem P2_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} (hA : P2 A) (hB : P2 B) (hC : P2 C) : P2 (A ∪ B ∪ C) := by
  -- First, merge `A` and `B`.
  have hAB : P2 (A ∪ B) := P2_union hA hB
  -- Then, merge the result with `C`.
  have hABC : P2 ((A ∪ B) ∪ C) := P2_union hAB hC
  -- Rewrite with associativity of union.
  simpa [Set.union_assoc] using hABC

theorem P3_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P3 A) (hB : P3 B) : P3 (Set.image (fun x : X × Y => (x.1, x.2)) (A ×ˢ B)) := by
  intro x hx
  rcases hx with ⟨⟨a, b⟩, hmem, rfl⟩
  have ha : a ∈ interior (closure A) := hA hmem.1
  have hb : b ∈ interior (closure B) := hB hmem.2
  have hprod : (a, b) ∈ interior (closure A) ×ˢ interior (closure B) := by
    exact ⟨ha, hb⟩
  simpa [closure_prod_eq, interior_prod_eq] using hprod

theorem P1_bUnion {X : Type*} [TopologicalSpace X] {ι : Sort _} {s : Set ι} (f : ι → Set X) (h : ∀ i ∈ s, P1 (f i)) : P1 (⋃ i ∈ s, f i) := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hx_i⟩
  rcases Set.mem_iUnion.mp hx_i with ⟨hi_mem_s, hx_fi⟩
  have hP1 : P1 (f i) := h i hi_mem_s
  have hx_cl : x ∈ closure (interior (f i)) := hP1 hx_fi
  have hsubset :
      closure (interior (f i)) ⊆ closure (interior (⋃ i ∈ s, f i)) := by
    have hsub : (f i : Set X) ⊆ ⋃ i ∈ s, f i := by
      intro y hy
      -- membership in the inner union over proofs `i ∈ s`
      have hinner : y ∈ ⋃ (hi : i ∈ s), f i := by
        refine Set.mem_iUnion.mpr ?_
        exact ⟨hi_mem_s, hy⟩
      -- membership in the outer union over indices `i`
      refine Set.mem_iUnion.mpr ?_
      exact ⟨i, hinner⟩
    exact closure_mono (interior_mono hsub)
  exact hsubset hx_cl

theorem P2_univ {X : Type*} [TopologicalSpace X] : P2 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P3_univ {X : Type*} [TopologicalSpace X] : P3 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P3_image_embedding {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) (hf : Embedding f) {A : Set X} : P3 (f '' A) → P3 A := by
  classical
  intro hP3
  intro x hxA
  -- `f x` lies in the interior of the closure of the image of `A`
  have hfx_int : f x ∈ interior (closure (f '' A)) := by
    have : f x ∈ (f '' A) := ⟨x, hxA, rfl⟩
    exact hP3 this
  -- Let `U` be the preimage of that interior
  let U : Set X := f ⁻¹' interior (closure (f '' A))
  have hU_open : IsOpen U := by
    have : IsOpen (interior (closure (f '' A))) := isOpen_interior
    simpa [U] using this.preimage hf.continuous
  have hxU : x ∈ U := by
    have : f x ∈ interior (closure (f '' A)) := hfx_int
    simpa [U, Set.mem_preimage] using this
  -- Show: `U ⊆ closure A`
  have hU_subset : (U : Set X) ⊆ closure (A : Set X) := by
    intro y hyU
    -- `f y` is in the interior, hence in the closure
    have hy_int : f y ∈ interior (closure (f '' A)) := by
      simpa [U, Set.mem_preimage] using hyU
    have hy_cl : f y ∈ closure (f '' A) := interior_subset hy_int
    -- If already in the closure we're done
    by_cases h_clA : y ∈ closure (A : Set X)
    · exact h_clA
    -- Otherwise derive a contradiction
    · have hOpenCompl : IsOpen ((closure (A : Set X))ᶜ) :=
        isClosed_closure.isOpen_compl
      -- Obtain an open set `V` in `Y` whose preimage is this complement
      rcases (hf.inducing.isOpen_iff).1 hOpenCompl with ⟨V, hVopen, hVpre⟩
      -- `y` is in the complement, so `f y ∈ V`
      have hyV : f y ∈ V := by
        have hyCompl : y ∈ ((closure (A : Set X))ᶜ) := by
          simpa using h_clA
        have : y ∈ f ⁻¹' V := by
          simpa [hVpre] using hyCompl
        simpa [Set.mem_preimage] using this
      -- Show that `V` is disjoint from `f '' A`
      have h_disjoint : V ∩ f '' A = (∅ : Set Y) := by
        apply Set.eq_empty_iff_forall_not_mem.2
        intro w hw
        rcases hw.2 with ⟨z, hzA, rfl⟩
        have hz_pre : z ∈ f ⁻¹' V := by
          change f z ∈ V
          exact hw.1
        have hz_not_cl : z ∈ ((closure (A : Set X))ᶜ) := by
          simpa [hVpre] using hz_pre
        have hz_cl : z ∈ closure (A : Set X) := subset_closure hzA
        exact (hz_not_cl hz_cl).elim
      -- But `f y` is in the closure of `f '' A`, so every neighborhood meets it
      have h_ne : (V ∩ f '' A).Nonempty :=
        (mem_closure_iff).1 hy_cl V hVopen hyV
      simpa [h_disjoint] using h_ne
  -- `U` is an open neighborhood of `x` contained in `closure A`
  have hU_to_int : (U : Set X) ⊆ interior (closure (A : Set X)) :=
    interior_maximal hU_subset hU_open
  have : x ∈ interior (closure (A : Set X)) := hU_to_int hxU
  exact this

theorem P2_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P2 A) (hB : P2 B) : P2 (Set.image (fun x : X × Y => (x.1, x.2)) (A ×ˢ B)) := by
  intro x hx
  rcases hx with ⟨⟨a, b⟩, hmem, rfl⟩
  have ha : a ∈ interior (closure (interior A)) := hA hmem.1
  have hb : b ∈ interior (closure (interior B)) := hB hmem.2
  have hprod :
      (a, b) ∈
        interior (closure (interior A)) ×ˢ
          interior (closure (interior B)) := by
    exact ⟨ha, hb⟩
  simpa [closure_prod_eq, interior_prod_eq] using hprod

theorem P3_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} : P3 B → P3 (e.symm '' B) := by
  exact (P3_image_homeomorph (e.symm)).1

theorem P1_compl_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P1 (Aᶜ) := by
  exact P1_of_P2 (A := Aᶜ) (P2_compl_of_closed (A := A) hA)

theorem P1_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P1 A) (hB : P1 B) : P1 (Set.image (fun x : X × Y => (x.1, x.2)) (A ×ˢ B)) := by
  intro x hx
  rcases hx with ⟨⟨a, b⟩, hmem, rfl⟩
  have ha : a ∈ closure (interior A) := hA hmem.1
  have hb : b ∈ closure (interior B) := hB hmem.2
  have hprod : (a, b) ∈ closure (interior A) ×ˢ closure (interior B) := by
    exact ⟨ha, hb⟩
  simpa [closure_prod_eq, interior_prod_eq] using hprod

theorem P1_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} : P1 B → P1 (e.symm '' B) := by
  intro hB
  exact ((P1_image_homeomorph (e.symm) (A := B))).1 hB

theorem P3_compl_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P3 (Aᶜ) := by
  simpa using (P3_of_open (A := Aᶜ) hA.isOpen_compl)

theorem P2_iUnion_directed {X : Type*} [TopologicalSpace X] {ι : Type*} {s : ι → Set X} (hdir : Directed (· ⊆ ·) s) (h : ∀ i, P2 (s i)) : P2 (⋃ i, s i) := by
  simpa using (P2_iUnion (s := s) h)

theorem P2_bUnion {X : Type*} [TopologicalSpace X] {ι : Sort _} {s : Set ι} (f : ι → Set X) (h : ∀ i ∈ s, P2 (f i)) : P2 (⋃ i ∈ s, f i) := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hx_i⟩
  rcases Set.mem_iUnion.mp hx_i with ⟨hi_mem_s, hx_fi⟩
  have hP2i : P2 (f i) := h i hi_mem_s
  have hx_int : x ∈ interior (closure (interior (f i))) := hP2i hx_fi
  have hsubset :
      interior (closure (interior (f i))) ⊆
        interior (closure (interior (⋃ i ∈ s, f i))) := by
    -- Start with the basic inclusion `f i ⊆ ⋃ i ∈ s, f i`.
    have hsub : (f i : Set X) ⊆ ⋃ i ∈ s, f i := by
      intro y hy
      -- Inner union over the proof `i ∈ s`.
      have hinner : y ∈ ⋃ (hi : i ∈ s), f i := by
        refine Set.mem_iUnion.mpr ?_
        exact ⟨hi_mem_s, hy⟩
      -- Outer union over the index `i`.
      refine Set.mem_iUnion.mpr ?_
      exact ⟨i, hinner⟩
    -- Now propagate the inclusion through `interior`, `closure`, `interior`.
    have hsub_int : interior (f i) ⊆ interior (⋃ i ∈ s, f i) :=
      interior_mono hsub
    have hsub_cl : closure (interior (f i)) ⊆
        closure (interior (⋃ i ∈ s, f i)) :=
      closure_mono hsub_int
    exact interior_mono hsub_cl
  exact hsubset hx_int

theorem P3_bUnion {X : Type*} [TopologicalSpace X] {ι : Sort _} {s : Set ι} (f : ι → Set X) (h : ∀ i ∈ s, P3 (f i)) : P3 (⋃ i ∈ s, f i) := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hx_i⟩
  rcases Set.mem_iUnion.mp hx_i with ⟨hi_mem_s, hx_fi⟩
  have hP3i : P3 (f i) := h i hi_mem_s
  have hx_int : x ∈ interior (closure (f i)) := hP3i hx_fi
  have hsubset :
      interior (closure (f i)) ⊆
        interior (closure (⋃ i ∈ s, f i)) := by
    -- First, show `f i ⊆ ⋃ i ∈ s, f i`.
    have hsub : (f i : Set X) ⊆ ⋃ i ∈ s, f i := by
      intro y hy
      -- Membership in the inner union over proofs `i ∈ s`.
      have hinner : y ∈ ⋃ (hi : i ∈ s), f i := by
        refine Set.mem_iUnion.mpr ?_
        exact ⟨hi_mem_s, hy⟩
      -- Membership in the outer union over indices `i`.
      refine Set.mem_iUnion.mpr ?_
      exact ⟨i, hinner⟩
    -- Propagate the inclusion through `closure` and `interior`.
    have hsub_cl : closure (f i) ⊆ closure (⋃ i ∈ s, f i) :=
      closure_mono hsub
    exact interior_mono hsub_cl
  exact hsubset hx_int

theorem P2_iff_P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense (interior A)) : P2 A ↔ P3 A := by
  constructor
  · intro hP2
    exact P3_of_P2 hP2
  · intro _hP3
    exact P2_of_dense_interior h

theorem P3_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] (A : Set X) : P3 A := by
  intro x hx
  -- In a subsingleton space, a nonempty set is the whole space.
  have hA_univ : (A : Set X) = Set.univ := by
    ext y
    constructor
    · intro _; simp
    · intro _
      have h_eq : y = x := Subsingleton.elim _ _
      simpa [h_eq] using hx
  -- Rewrite the goal using `hA_univ`.
  simpa [hA_univ, closure_univ, interior_univ] using (by
    -- `x` is trivially in the interior of the closure of `univ`.
    simpa [closure_univ, interior_univ] : x ∈ interior (closure (Set.univ : Set X)))

theorem P1_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] (A : Set X) : P1 A := by
  exact P1_of_P2 (A := A) (P2_subsingleton A)

theorem P2_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : P2 A) : P2 (A ×ˢ (Set.univ : Set Y)) := by
  intro x hx
  rcases x with ⟨a, b⟩
  have ha : a ∈ interior (closure (interior A)) := hA hx.1
  have hb : b ∈ interior (closure (interior (Set.univ : Set Y))) := by
    simpa [interior_univ, closure_univ] using (Set.mem_univ b)
  have hprod :
      (a, b) ∈
        interior (closure (interior A)) ×ˢ
          interior (closure (interior (Set.univ : Set Y))) := by
    exact ⟨ha, hb⟩
  simpa [closure_prod_eq, interior_prod_eq, interior_univ, closure_univ] using hprod

theorem P3_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : P3 A) : P3 (A ×ˢ (Set.univ : Set Y)) := by
  intro x hx
  rcases x with ⟨a, b⟩
  have ha : a ∈ interior (closure A) := hA hx.1
  have hb : b ∈ interior (closure (Set.univ : Set Y)) := by
    simpa [closure_univ, interior_univ] using (Set.mem_univ b)
  have hprod :
      (a, b) ∈
        interior (closure A) ×ˢ
          interior (closure (Set.univ : Set Y)) := by
    exact ⟨ha, hb⟩
  simpa [closure_prod_eq, interior_prod_eq, closure_univ, interior_univ] using hprod

theorem P2_iff_P1_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hD : Dense A) : P2 A ↔ P1 A := by
  classical
  constructor
  · intro hP2
    exact P1_of_P2 hP2
  · intro hP1
    intro x hx
    have hcl : closure (interior A) = (Set.univ : Set X) := by
      have h_eq := (P1_iff_dense_interior (A := A)).1 hP1
      simpa [hD.closure_eq] using h_eq
    simpa [hcl, interior_univ] using (Set.mem_univ x)

theorem P1_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : P1 A) : P1 (A ×ˢ (Set.univ : Set Y)) := by
  intro x hx
  rcases x with ⟨a, b⟩
  -- `a` is in `A`, hence in `closure (interior A)` by `hA`
  have ha : a ∈ closure (interior A) := hA hx.1
  -- `b` is trivially in the closure of the interior of `univ`
  have hb : b ∈ closure (interior (Set.univ : Set Y)) := by
    simpa [interior_univ, closure_univ] using (Set.mem_univ b)
  -- put the pieces together in the product
  have hprod :
      (a, b) ∈
        closure (interior A) ×ˢ
          closure (interior (Set.univ : Set Y)) := by
    exact ⟨ha, hb⟩
  -- rewrite the goal using the product rules for interior and closure
  simpa [closure_prod_eq, interior_prod_eq, interior_univ, closure_univ] using hprod

theorem P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → P1 (closure A) := by
  intro hP1
  intro x hx
  -- First inclusion: closure A ⊆ closure (interior A)
  have hsubset1 : (closure A : Set X) ⊆ closure (interior A) := by
    have : (closure A : Set X) ⊆ closure (closure (interior A)) :=
      closure_mono hP1
    simpa [closure_closure] using this
  -- Second inclusion: closure (interior A) ⊆ closure (interior (closure A))
  have hsubset2 :
      (closure (interior A) : Set X) ⊆ closure (interior (closure A)) := by
    have : (interior A : Set X) ⊆ interior (closure A) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    exact closure_mono this
  exact hsubset2 (hsubset1 hx)

theorem P1_prod_set {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P1 A) (hB : P1 B) : P1 (A ×ˢ B) := by
  intro x hx
  rcases x with ⟨a, b⟩
  have ha : a ∈ closure (interior A) := hA hx.1
  have hb : b ∈ closure (interior B) := hB hx.2
  have hprod : (a, b) ∈ closure (interior A) ×ˢ closure (interior B) := by
    exact ⟨ha, hb⟩
  simpa [closure_prod_eq, interior_prod_eq] using hprod

theorem P2_prod_set {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P2 A) (hB : P2 B) : P2 (A ×ˢ B) := by
  intro x hx
  rcases x with ⟨a, b⟩
  rcases hx with ⟨haA, hbB⟩
  have ha : a ∈ interior (closure (interior A)) := hA haA
  have hb : b ∈ interior (closure (interior B)) := hB hbB
  have hprod :
      (a, b) ∈
        interior (closure (interior A)) ×ˢ
          interior (closure (interior B)) := by
    exact ⟨ha, hb⟩
  simpa [closure_prod_eq, interior_prod_eq] using hprod

theorem P3_prod_set {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P3 A) (hB : P3 B) : P3 (A ×ˢ B) := by
  intro x hx
  rcases x with ⟨a, b⟩
  rcases hx with ⟨haA, hbB⟩
  have ha : a ∈ interior (closure A) := hA haA
  have hb : b ∈ interior (closure B) := hB hbB
  have hprod :
      (a, b) ∈ interior (closure A) ×ˢ interior (closure B) := by
    exact ⟨ha, hb⟩
  simpa [closure_prod_eq, interior_prod_eq] using hprod

theorem P1_sUnion_empty {X : Type*} [TopologicalSpace X] : P1 (⋃₀ (∅ : Set (Set X))) := by
  simpa [Set.sUnion_empty] using (P1_empty : P1 (∅ : Set X))

theorem P2_union_distrib {X : Type*} [TopologicalSpace X] {A B C : Set X} : P2 (A ∪ (B ∩ C)) ↔ P2 ((A ∪ B) ∩ (A ∪ C)) := by
  classical
  -- First, record the set-theoretic identity we need.
  have h_eq : (A ∪ (B ∩ C) : Set X) = (A ∪ B) ∩ (A ∪ C) := by
    ext x
    constructor
    · intro hx
      cases hx with
      | inl hA =>
          exact ⟨Or.inl hA, Or.inl hA⟩
      | inr hBC =>
          exact ⟨Or.inr hBC.1, Or.inr hBC.2⟩
    · intro hx
      rcases hx with ⟨hAB, hAC⟩
      cases hAB with
      | inl hA =>
          exact Or.inl hA
      | inr hB =>
          cases hAC with
          | inl hA =>
              exact Or.inl hA
          | inr hC =>
              exact Or.inr ⟨hB, hC⟩
  -- The desired equivalence now follows by rewriting with `h_eq`.
  constructor
  · intro hP2
    simpa [h_eq] using hP2
  · intro hP2
    simpa [h_eq] using hP2

theorem P3_prod_distrib {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : P3 A) (hB : P3 B) (hC : P3 C) : P3 (Set.image (fun xyz : X × Y × Z => (xyz.1, (xyz.2).1, (xyz.2).2)) (A ×ˢ B ×ˢ C)) := by
  intro xyz hx
  rcases hx with ⟨xyz0, hmem, rfl⟩
  rcases xyz0 with ⟨x, yz⟩
  rcases yz with ⟨y, z⟩
  -- Extract component-wise membership
  have hxA : x ∈ A := hmem.1
  have hyz : (y, z) ∈ B ×ˢ C := hmem.2
  have hyB : y ∈ B := hyz.1
  have hzC : z ∈ C := hyz.2
  -- Apply the P3 hypotheses
  have hx_int : x ∈ interior (closure A) := hA hxA
  have hy_int : y ∈ interior (closure B) := hB hyB
  have hz_int : z ∈ interior (closure C) := hC hzC
  -- Build interior membership for the (B ×ˢ C) part
  have hBC_int : (y, z) ∈ interior (closure (B ×ˢ C)) := by
    have : (y, z) ∈ interior (closure B) ×ˢ interior (closure C) := by
      exact ⟨hy_int, hz_int⟩
    simpa [closure_prod_eq, interior_prod_eq] using this
  -- Combine everything for the triple product
  have hprod :
      (x, (y, z)) ∈
        interior (closure A) ×ˢ interior (closure (B ×ˢ C)) := by
    exact ⟨hx_int, hBC_int⟩
  simpa [closure_prod_eq, interior_prod_eq] using hprod

theorem P1_sigma {α : Type*} {β : α → Type*} [∀ a, TopologicalSpace (β a)] (s : Set α) (t : ∀ a, Set (β a)) (h : ∀ a, P1 (t a)) : P1 {p : Sigma β | p.1 ∈ s ∧ p.2 ∈ t p.1} := by
  classical
  -- Put the target set in a local name.
  let S : Set (Sigma β) := {q | q.1 ∈ s ∧ q.2 ∈ t q.1}
  intro p hp
  -- Decompose the Σ–point.
  rcases p with ⟨a, b⟩
  -- Separate the component hypotheses.
  have ha : a ∈ s := hp.1
  have hb : b ∈ t a := hp.2
  -- Use the fibrewise `P1` assumption.
  have hb_cl : b ∈ closure (interior (t a)) := (h a) hb
  -- We prove that `(a , b)` lies in the closure of the interior of `S`.
  have h_cl : (⟨a, b⟩ : Sigma β) ∈ closure (interior S) := by
    -- Neighbourhood characterisation of `closure`.
    apply (mem_closure_iff).2
    intro U hU_open hU_mem
    -- Slice `U` along the fibre over `a`.
    let V : Set (β a) := {b' | (⟨a, b'⟩ : Sigma β) ∈ U}
    have hV_open : IsOpen V := by
      -- The map `b' ↦ (a , b')` is continuous.
      have hcont : Continuous fun b' : β a => (⟨a, b'⟩ : Sigma β) := by
        continuity
      simpa [V] using hU_open.preimage hcont
    have hbV : b ∈ V := by
      simpa [V] using hU_mem
    -- Because `b ∈ closure (interior (t a))`, `V` meets `interior (t a)`.
    have h_non : (V ∩ interior (t a)).Nonempty := by
      have := (mem_closure_iff).1 hb_cl V hV_open hbV
      simpa [Set.inter_comm] using this
    rcases h_non with ⟨b', hb'V, hb'int⟩
    --------------------------------------------------------------------
    -- Construct an auxiliary open set contained in `S`.
    --------------------------------------------------------------------
    -- Define a fibrewise set choosing `interior (t a')` when `a' ∈ s`.
    let F : ∀ a', Set (β a') := fun a' =>
      if h' : a' ∈ s then interior (t a') else ∅
    have hF_open : ∀ a', IsOpen (F a') := by
      intro a'
      by_cases h' : a' ∈ s
      · simpa [F, h'] using isOpen_interior
      · simpa [F, h'] using (isOpen_empty : IsOpen (∅ : Set (β a')))
    -- Turn it into a set of Σ.
    let W : Set (Sigma β) := {q | q.2 ∈ F q.1}
    have hW_open : IsOpen W := by
      -- Use the characterisation of open sets in Σ–types.
      refine (isOpen_sigma_iff).2 ?_
      intro a'
      have : {b'' : β a' | (⟨a', b''⟩ : Sigma β) ∈ W} = F a' := rfl
      simpa [this] using hF_open a'
    -- `W` is contained in `S`.
    have hW_sub : W ⊆ S := by
      intro q hq
      rcases q with ⟨a', b''⟩
      dsimp [W] at hq
      by_cases hsa' : a' ∈ s
      · -- Here `F a' = interior (t a')`.
        have hFdef : F a' = interior (t a') := by
          simp [F, hsa'] at *
        have hb''int : b'' ∈ interior (t a') := by
          simpa [hFdef] using hq
        exact And.intro hsa' (interior_subset hb''int)
      · -- Otherwise `F a' = ∅`, contradiction.
        have : b'' ∈ (∅ : Set (β a')) := by
          simpa [F, hsa'] using hq
        cases this
    -- The constructed point lies in `W`.
    have hqW : (⟨a, b'⟩ : Sigma β) ∈ W := by
      dsimp [W]
      have hFdef : F a = interior (t a) := by
        have : a ∈ s := ha
        simp [F, this]
      simpa [hFdef] using hb'int
    -- Since `W ⊆ S` and `W` is open, points of `W` are in `interior S`.
    have hsubsetW : (W : Set (Sigma β)) ⊆ interior S :=
      interior_maximal hW_sub hW_open
    have hq_intS : (⟨a, b'⟩ : Sigma β) ∈ interior S := hsubsetW hqW
    -- `(a , b')` is also in `U`.
    have hqU : (⟨a, b'⟩ : Sigma β) ∈ U := by
      have : b' ∈ V := hb'V
      simpa [V] using this
    -- Provide the witness required by the closure criterion.
    exact ⟨⟨a, b'⟩, hqU, hq_intS⟩
  -- Finish: unravel `S`.
  simpa [S] using h_cl

theorem P3_iff_P2_closed_or_open {X : Type*} [TopologicalSpace X] {A : Set X} (h : IsClosed A ∨ IsOpen A) : P3 A ↔ P2 A := by
  classical
  cases h with
  | inl hClosed =>
      simpa using (P3_iff_P2_of_closed (A := A) hClosed)
  | inr hOpen =>
      simpa using ((P2_iff_P3_of_open (A := A) hOpen).symm)

theorem P3_diff_closed {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P3 A) (hB : IsClosed B) : P3 (A \ B) := by
  intro x hx
  -- `hx` gives membership in `A` and not in `B`.
  have hxA : x ∈ A := hx.1
  have hxNotB : x ∈ (Bᶜ) := hx.2
  -- `hA` yields interior membership w.r.t. `closure A`.
  have hx_int : x ∈ interior (closure A) := hA hxA
  -- Define the auxiliary open neighbourhood
  let U : Set X := interior (closure A) ∩ Bᶜ
  have hU_open : IsOpen U := by
    dsimp [U]
    exact (isOpen_interior).inter hB.isOpen_compl
  -- Show that `U ⊆ closure (A \ B)`.
  have hU_subset : (U : Set X) ⊆ closure (A \ B) := by
    intro y hyU
    -- Decompose the membership information.
    have hy_int : y ∈ interior (closure A) := hyU.1
    have hyNotB : y ∈ (Bᶜ) := hyU.2
    -- From interior to closure.
    have hy_clA : y ∈ closure A := interior_subset hy_int
    -- Use the neighbourhood characterization of closure.
    have : y ∈ closure (A \ B) := by
      apply (mem_closure_iff).2
      intro V hV_open hyV
      -- Refine the neighbourhood so that it avoids `B`.
      have hW_open : IsOpen (V ∩ Bᶜ) := hV_open.inter hB.isOpen_compl
      have hyW : y ∈ V ∩ Bᶜ := ⟨hyV, hyNotB⟩
      -- Since `y ∈ closure A`, this refined neighbourhood meets `A`.
      rcases (mem_closure_iff).1 hy_clA (V ∩ Bᶜ) hW_open hyW with ⟨z, hzW, hzA⟩
      -- Extract the required witness in `A \ B`.
      have hzV : z ∈ V := hzW.1
      have hzNotB : z ∈ (Bᶜ) := hzW.2
      exact ⟨z, ⟨hzV, ⟨hzA, hzNotB⟩⟩⟩
    exact this
  -- `x` certainly belongs to `U`.
  have hxU : x ∈ U := by
    dsimp [U]
    exact ⟨hx_int, hxNotB⟩
  -- Maximality of the interior gives the desired membership.
  have hU_to_int : (U : Set X) ⊆ interior (closure (A \ B)) :=
    interior_maximal hU_subset hU_open
  exact hU_to_int hxU

theorem P1_diff_of_closed {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P1 A) (hB : IsClosed B) : P1 (A \ B) := by
  classical
  intro x hx
  -- `x` is in `A`, hence in the closure of `interior A` by `hA`.
  have hx_cl : x ∈ closure (interior A) := hA hx.1
  -- We prove that `x` is in the closure of `interior (A \ B)`.
  have : x ∈ closure (interior (A \ B)) := by
    -- Neighbourhood characterisation of the closure.
    apply (mem_closure_iff).2
    intro V hVopen hxV
    -- Refine the neighbourhood to avoid `B`.
    have hWopen : IsOpen (V ∩ Bᶜ) := hVopen.inter hB.isOpen_compl
    have hxW : x ∈ V ∩ Bᶜ := by
      exact ⟨hxV, hx.2⟩
    -- This refined neighbourhood meets `interior A`.
    have h_non : ((V ∩ Bᶜ) ∩ interior A).Nonempty := by
      have := (mem_closure_iff).1 hx_cl (V ∩ Bᶜ) hWopen hxW
      simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using this
    rcases h_non with ⟨y, hyW, hyIntA⟩
    -- `y` will be shown to lie in `interior (A \ B)`.
    have hyInt : y ∈ interior (A \ B) := by
      -- Consider the open set `U = interior A ∩ Bᶜ`.
      have hUopen : IsOpen (interior A ∩ Bᶜ) :=
        isOpen_interior.inter hB.isOpen_compl
      have hU_subset : (interior A ∩ Bᶜ : Set X) ⊆ A \ B := by
        intro z hz
        exact ⟨(interior_subset : interior A ⊆ A) hz.1, hz.2⟩
      have hyU : y ∈ interior A ∩ Bᶜ := by
        have hyNotB : y ∈ Bᶜ := hyW.2
        exact ⟨hyIntA, hyNotB⟩
      exact
        mem_interior.2 ⟨interior A ∩ Bᶜ, hU_subset, hUopen, hyU⟩
    -- Provide the required witness in `V ∩ interior (A \ B)`.
    have hyV : y ∈ V := hyW.1
    exact ⟨y, hyV, hyInt⟩
  exact this

theorem P2_diff_closed {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P2 A) (hB : IsClosed B) : P2 (A \ B) := by
  intro x hx
  -- `hx` gives the two components of membership.
  have hx_int : x ∈ interior (closure (interior A)) := by
    exact hA hx.1
  -- Define an auxiliary open neighbourhood that avoids `B`.
  let U : Set X := interior (closure (interior A)) ∩ Bᶜ
  have hU_open : IsOpen U := by
    dsimp [U]
    exact isOpen_interior.inter hB.isOpen_compl
  -- Show that this neighbourhood is contained in the desired closure.
  have hU_subset : (U : Set X) ⊆ closure (interior (A \ B)) := by
    intro y hyU
    -- Decompose the membership information.
    have hy_int : y ∈ interior (closure (interior A)) := hyU.1
    have hy_notB : y ∈ Bᶜ := hyU.2
    have hy_cl : y ∈ closure (interior A) := interior_subset hy_int
    -- Use the neighbourhood characterisation of the closure.
    have : y ∈ closure (interior (A \ B)) := by
      apply (mem_closure_iff).2
      intro V hVopen hyV
      -- Refine the neighbourhood so that it avoids `B`.
      have hW_open : IsOpen (V ∩ Bᶜ) := hVopen.inter hB.isOpen_compl
      have hyW : y ∈ V ∩ Bᶜ := ⟨hyV, hy_notB⟩
      -- Because `y ∈ closure (interior A)`, this refined neighbourhood meets `interior A`.
      have h_non : ((V ∩ Bᶜ) ∩ interior A).Nonempty := by
        have := (mem_closure_iff).1 hy_cl (V ∩ Bᶜ) hW_open hyW
        simpa [Set.inter_assoc, Set.inter_left_comm] using this
      rcases h_non with ⟨z, ⟨⟨hzV, hzNotB⟩, hzIntA⟩⟩
      -- `z` is in `interior A` and avoids `B`; show it is in `interior (A \ B)`.
      have hz_int_diff : z ∈ interior (A \ B) := by
        -- The open set `interior A ∩ Bᶜ` is contained in `A \ B`.
        have hOpen : IsOpen (interior A ∩ Bᶜ) :=
          isOpen_interior.inter hB.isOpen_compl
        have hSub : (interior A ∩ Bᶜ : Set X) ⊆ A \ B := by
          intro w hw
          exact ⟨(interior_subset : interior A ⊆ A) hw.1, hw.2⟩
        have hzU : z ∈ interior A ∩ Bᶜ := ⟨hzIntA, hzNotB⟩
        exact (mem_interior.2 ⟨_, hSub, hOpen, hzU⟩)
      -- Provide the witness in `V ∩ interior (A \ B)`.
      exact ⟨z, hzV, hz_int_diff⟩
    exact this
  -- The point `x` lies in `U`.
  have hxU : x ∈ U := by
    dsimp [U]
    exact ⟨hx_int, hx.2⟩
  -- Maximality of the interior yields the desired membership.
  have h_in : x ∈ interior (closure (interior (A \ B))) :=
    (interior_maximal hU_subset hU_open) hxU
  exact h_in

theorem P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense (interior A)) : P3 A := by
  exact P3_of_P2 (A := A) (P2_of_dense_interior (A := A) h)

theorem P1_closure_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : P1 (closure A) := by
  exact (P1_closure (A := A)) (P1_of_P2 (A := A) hA)

theorem P1_prod_empty {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : P1 (A ×ˢ (∅ : Set Y)) := by
  intro x hx
  rcases hx with ⟨_, hFalse⟩
  cases hFalse

theorem P2_prod_empty {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : P2 (A ×ˢ (∅ : Set Y)) := by
  intro x hx
  rcases hx with ⟨_, hY⟩
  cases hY

theorem P3_prod_empty {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : P3 (A ×ˢ (∅ : Set Y)) := by
  intro x hx
  cases hx.2

theorem P2_finite_iUnion {X : Type*} [TopologicalSpace X] {ι : Type*} [Fintype ι] {s : ι → Set X} (h : ∀ i, P2 (s i)) : P2 (⋃ i, s i) := by
  simpa using (P2_iUnion (s := s) h)

theorem P2_image_embedding {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} (hf : Embedding f) {A : Set X} : P2 (f '' A) → P2 A := by
  classical
  intro hP2
  intro x hxA
  -- Image point satisfies the `P2` condition.
  have hfx :
      f x ∈ interior (closure (interior (f '' A))) :=
    hP2 ⟨x, hxA, rfl⟩
  -- An auxiliary open neighbourhood on the source.
  set U : Set X := f ⁻¹' interior (closure (interior (f '' A))) with hUdef
  have hU_open : IsOpen U := by
    have : IsOpen (interior (closure (interior (f '' A)))) :=
      isOpen_interior
    simpa [hUdef] using this.preimage hf.continuous
  have hxU : x ∈ U := by
    simpa [hUdef, Set.mem_preimage] using hfx
  ----------------------------------------------------------------
  -- Main inclusion: `U ⊆ closure (interior A)`.
  ----------------------------------------------------------------
  have hU_subset : (U : Set X) ⊆ closure (interior A) := by
    intro y hyU
    -- Image of `y` lies in the closure.
    have hfy_cl :
        f y ∈ closure (interior (f '' A)) := by
      have : f y ∈ interior (closure (interior (f '' A))) := by
        simpa [hUdef, Set.mem_preimage] using hyU
      exact interior_subset this
    -- If `y` is already in the desired closure we are done.
    by_cases hmem : y ∈ closure (interior A)
    · exact hmem
    -- Otherwise derive a contradiction.
    have hCopen : IsOpen ((closure (interior A))ᶜ) :=
      isClosed_closure.isOpen_compl
    have hyC : y ∈ (closure (interior A))ᶜ := hmem
    -- Transport openness via the embedding.
    obtain ⟨V, hVopen, hVpre⟩ :=
      (hf.inducing.isOpen_iff).1 hCopen
    have hyV : f y ∈ V := by
      have : y ∈ f ⁻¹' V := by
        simpa [hVpre] using hyC
      simpa [Set.mem_preimage] using this
    ----------------------------------------------------------------
    -- Show `V` is disjoint from `interior (f '' A)`.
    ----------------------------------------------------------------
    have hV_disj : V ∩ interior (f '' A) = (∅ : Set Y) := by
      apply Set.eq_empty_iff_forall_not_mem.2
      intro w hw
      rcases hw with ⟨hwV, hwInt⟩
      -- Lift `w` to the source.
      have hwImg : w ∈ f '' A := interior_subset hwInt
      rcases hwImg with ⟨z, hzA, hw_eq⟩
      -- Obtain an open nbhd witnessing `w ∈ interior (f '' A)`.
      rcases(mem_interior.1 hwInt) with ⟨W, hWsub, hWopen, hwW⟩
      -- Pull back this nbhd.
      let H : Set X := f ⁻¹' W
      have hHopen : IsOpen H :=
        hWopen.preimage hf.continuous
      have hHsub : (H : Set X) ⊆ A := by
        intro t htH
        have hf_t_W : f t ∈ W := htH
        have hf_t_img : f t ∈ f '' A := hWsub hf_t_W
        rcases hf_t_img with ⟨a', ha'A, h_eq'⟩
        have ht_eq : t = a' := by
          apply hf.injective
          exact h_eq'.symm
        simpa [ht_eq] using ha'A
      have hzH : z ∈ H := by
        change f z ∈ W
        simpa [hw_eq] using hwW
      -- Hence `z ∈ interior A`.
      have hz_intA : z ∈ interior A :=
        mem_interior.2 ⟨H, hHsub, hHopen, hzH⟩
      -- And thus `z ∈ closure (interior A)`.
      have hz_cl : z ∈ closure (interior A) :=
        subset_closure hz_intA
      -- Yet `f z = w ∈ V`, so `z` is also in the preimage of `V`.
      have hz_pre : z ∈ f ⁻¹' V := by
        change f z ∈ V
        simpa [hw_eq] using hwV
      have hz_not : z ∈ (closure (interior A))ᶜ := by
        simpa [hVpre] using hz_pre
      exact (hz_not hz_cl).elim
    ----------------------------------------------------------------
    -- But `f y` is in the closure of that interior — contradiction.
    ----------------------------------------------------------------
    have hNon : (V ∩ interior (f '' A)).Nonempty :=
      (mem_closure_iff).1 hfy_cl V hVopen hyV
    simpa [hV_disj] using hNon
  ----------------------------------------------------------------
  -- Maximality of the interior gives the desired membership for `x`.
  ----------------------------------------------------------------
  have hx_int :
      x ∈ interior (closure (interior A)) :=
    (interior_maximal hU_subset hU_open) hxU
  exact hx_int

theorem P1_image_embedding {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} (hf : Embedding f) {A : Set X} : P1 (f '' A) → P1 A := by
  intro hP1
  intro x hxA
  classical
  -- `f x` is in the closure of the interior of the image.
  have hfx_cl : f x ∈ closure (interior (f '' A)) :=
    hP1 ⟨x, hxA, rfl⟩
  -- We show that `x` is in the closure of the interior of `A`.
  have : x ∈ closure (interior A) := by
    -- Use the neighbourhood characterisation of the closure.
    apply (mem_closure_iff).2
    intro V hVopen hxV
    -- Find an open set `W` in `Y` whose preimage is `V`.
    obtain ⟨W, hWopen, hWpre⟩ :=
      (hf.inducing.isOpen_iff).1 hVopen
    -- `f x` belongs to `W`.
    have hxW : f x ∈ W := by
      have : x ∈ (f ⁻¹' W) := by
        simpa [hWpre] using hxV
      simpa [Set.mem_preimage] using this
    -- `W` meets `interior (f '' A)`.
    have h_non : (W ∩ interior (f '' A)).Nonempty :=
      (mem_closure_iff).1 hfx_cl W hWopen hxW
    rcases h_non with ⟨y, hyW, hyInt⟩
    -- Write `y` as `f z` with `z ∈ A`.
    have hyImg : y ∈ f '' A := interior_subset hyInt
    rcases hyImg with ⟨z, hzA, rfl⟩
    -- Show `z ∈ V`.
    have hzV : z ∈ V := by
      have : f z ∈ W := hyW
      have : z ∈ f ⁻¹' W := by
        simpa [Set.mem_preimage] using this
      simpa [hWpre] using this
    -- Show `z ∈ interior A`.
    have hzIntA : z ∈ interior A := by
      -- From `f z ∈ interior (f '' A)` obtain a suitable open neighbourhood.
      rcases mem_interior.1 hyInt with ⟨U', hU'sub, hU'open, hzyU'⟩
      -- Pull it back to `X`.
      let H : Set X := f ⁻¹' U'
      have hHopen : IsOpen H := hU'open.preimage hf.continuous
      have hzH : z ∈ H := by
        dsimp [H]; simpa using hzyU'
      -- `H` is contained in `A`.
      have hHsubA : (H : Set X) ⊆ A := by
        intro t htH
        have hftU' : f t ∈ U' := htH
        have hftImg : f t ∈ f '' A := hU'sub hftU'
        rcases hftImg with ⟨w, hwA, hw_eq⟩
        have ht_eq : t = w := by
          apply hf.injective
          exact hw_eq.symm
        simpa [ht_eq] using hwA
      exact
        mem_interior.2 ⟨H, hHsubA, hHopen, hzH⟩
    -- Provide the required witness in `V ∩ interior A`.
    exact ⟨z, hzV, hzIntA⟩
  exact this

theorem P1_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → closure (interior A) = closure A := by
  intro hP1
  exact (P1_iff_dense_interior (A := A)).1 hP1

theorem P3_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} : P3 A → interior (closure A) = interior (closure (closure A)) := by
  intro _
  simp [closure_closure]

theorem P3_union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X} (hA : P3 A) (hB : P3 B) (hC : P3 C) (hD : P3 D) : P3 (A ∪ B ∪ C ∪ D) := by
  have hABC : P3 (A ∪ B ∪ C) := P3_union_three hA hB hC
  have hABCD : P3 ((A ∪ B ∪ C) ∪ D) := P3_union hABC hD
  simpa [Set.union_assoc] using hABCD

theorem P1_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} (hA : P1 A) (hB : P1 B) (hC : P1 C) : P1 (A ∪ B ∪ C) := by
  -- First, merge `A` and `B`.
  have hAB : P1 (A ∪ B) := P1_union hA hB
  -- Then, merge the result with `C`.
  have hABC : P1 ((A ∪ B) ∪ C) := P1_union hAB hC
  -- Rewrite with associativity of union.
  simpa [Set.union_assoc] using hABC

theorem P2_union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X} (hA : P2 A) (hB : P2 B) (hC : P2 C) (hD : P2 D) : P2 (A ∪ B ∪ C ∪ D) := by
  have hABC : P2 (A ∪ B ∪ C) := P2_union_three hA hB hC
  have hABCD : P2 ((A ∪ B ∪ C) ∪ D) := P2_union hABC hD
  simpa [Set.union_assoc] using hABCD

theorem P1_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : P1 A) (hB : P1 B) (hC : P1 C) : P1 (Set.image (fun xyz : X × Y × Z => (xyz.1, (xyz.2).1, (xyz.2).2)) (A ×ˢ B ×ˢ C)) := by
  -- Unpack the image membership: obtain a pre-image point in the product set.
  intro xyz hxyz
  rcases hxyz with ⟨xyz0, hmem0, rfl⟩
  -- Decompose the triple point into its three coordinates.
  rcases xyz0 with ⟨x, yz⟩
  rcases yz with ⟨y, z⟩
  -- `hmem0` gives component-wise membership in the product set `A ×ˢ B ×ˢ C`.
  rcases hmem0 with ⟨hxA, hyzBC⟩
  rcases hyzBC with ⟨hyB, hzC⟩
  -- Apply the `P1` hypotheses to each coordinate separately.
  have hx_cl : x ∈ closure (interior A) := hA hxA
  have hy_cl : y ∈ closure (interior B) := hB hyB
  have hz_cl : z ∈ closure (interior C) := hC hzC
  ------------------------------------------------------------------
  -- Step 1: treat the `(y , z)` block.
  ------------------------------------------------------------------
  have h_BC_cl : (y, z) ∈ closure (interior (B ×ˢ C)) := by
    -- First place `(y , z)` in the product of the closures,
    -- then rewrite with the product rules for `closure` and `interior`.
    have hprod : (y, z) ∈ closure (interior B) ×ˢ closure (interior C) :=
      ⟨hy_cl, hz_cl⟩
    simpa [closure_prod_eq, interior_prod_eq] using hprod
  ------------------------------------------------------------------
  -- Step 2: assemble the three coordinates.
  ------------------------------------------------------------------
  have h_xyz_cl : (x, (y, z)) ∈ closure (interior (A ×ˢ B ×ˢ C)) := by
    -- Again use the product rules, now for the outer product.
    have hprod :
        (x, (y, z)) ∈ closure (interior A) ×ˢ
          closure (interior (B ×ˢ C)) := by
      exact ⟨hx_cl, h_BC_cl⟩
    simpa [closure_prod_eq, interior_prod_eq] using hprod
  ------------------------------------------------------------------
  -- Step 3: upgrade to the required set (the image),
  --         using monotonicity of `interior` and `closure`.
  ------------------------------------------------------------------
  -- The product set is contained in its image under the (essentially
  -- identity) map, hence the same is true for the corresponding
  -- closures of interiors.
  have hsub :
      (A ×ˢ B ×ˢ C : Set (X × Y × Z)) ⊆
        Set.image
          (fun xyz : X × Y × Z =>
            (xyz.1, (xyz.2).1, (xyz.2).2))
          (A ×ˢ B ×ˢ C) := by
    intro xyz' hxyz'
    exact ⟨xyz', hxyz', rfl⟩
  have hsubset_cl :
      closure (interior (A ×ˢ B ×ˢ C)) ⊆
        closure (interior (Set.image
          (fun xyz : X × Y × Z => (xyz.1, (xyz.2).1, (xyz.2).2))
          (A ×ˢ B ×ˢ C))) :=
    closure_mono (interior_mono hsub)
  ------------------------------------------------------------------
  -- Step 4: conclude.
  ------------------------------------------------------------------
  exact hsubset_cl h_xyz_cl