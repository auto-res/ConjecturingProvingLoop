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


theorem P2_subset_P3 {A : Set X} (h : P2 A) : P3 A := by
  exact subset_trans h (interior_mono (closure_mono interior_subset))

theorem P1_union {A B : Set X} (hA : P1 A) (hB : P1 B) : P1 (A ∪ B) := by
  -- We must prove `(A ∪ B) ⊆ closure (interior (A ∪ B))`
  intro x hx
  cases hx with
  | inl hAx =>
      -- `x` comes from `A`
      have hxA : x ∈ closure (interior A) := hA hAx
      have h_subset : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono (interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B))
      exact h_subset hxA
  | inr hBx =>
      -- `x` comes from `B`
      have hxB : x ∈ closure (interior B) := hB hBx
      have h_subset : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono (interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B))
      exact h_subset hxB

theorem P1_closed_of_P2 {A : Set X} (h : P2 A) (hcl : IsClosed A) : P1 A := by
  exact subset_trans h interior_subset

theorem P2_of_closure_eq {A : Set X} (h_eq : closure A = interior A) : P2 A := by
  intro x hx
  have hx_closure : (x : X) ∈ closure A := subset_closure hx
  have hx_int : (x : X) ∈ interior A := by
    simpa [h_eq] using hx_closure
  have h_subset : (interior A : Set X) ⊆ interior (closure (interior A)) :=
    interior_maximal subset_closure isOpen_interior
  exact h_subset hx_int

theorem P2_open {A : Set X} (h_open : IsOpen A) : P2 A := by
  intro x hx
  -- Since `A` is open, it is an open neighbourhood of `x`
  -- that is contained in `closure A`.
  have h₁ : x ∈ interior (closure A) := by
    exact (mem_interior.mpr ⟨A, subset_closure, h_open, hx⟩)
  simpa [h_open.interior_eq] using h₁

theorem interior_subset_of_P1 {A : Set X} (h : P1 A) : interior A ⊆ interior (closure A) := by
  exact interior_mono subset_closure

theorem P1_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : P1 A := by
  exact subset_trans h interior_subset

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P2 A) (hB : P2 B) : P2 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hAx =>
      have hxA : x ∈ interior (closure (interior A)) := hA hAx
      have h_subset :
          (interior (closure (interior A)) : Set X) ⊆
            interior (closure (interior (A ∪ B))) :=
        interior_mono
          (closure_mono
            (interior_mono
              (by
                simpa using
                  (Set.subset_union_left : (A : Set X) ⊆ A ∪ B))))
      exact h_subset hxA
  | inr hBx =>
      have hxB : x ∈ interior (closure (interior B)) := hB hBx
      have h_subset :
          (interior (closure (interior B)) : Set X) ⊆
            interior (closure (interior (A ∪ B))) :=
        interior_mono
          (closure_mono
            (interior_mono
              (by
                simpa using
                  (Set.subset_union_right : (B : Set X) ⊆ A ∪ B))))
      exact h_subset hxB

theorem P3_open {X : Type*} [TopologicalSpace X] {A : Set X} (h_open : IsOpen A) : P3 A := by
  intro x hx
  have hx_int : x ∈ interior A := by
    simpa [h_open.interior_eq] using hx
  have h_subset : (interior A : Set X) ⊆ interior (closure A) :=
    interior_mono subset_closure
  exact h_subset hx_int

theorem closure_eq_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : closure A = closure (interior A) := by
  -- We prove the two inclusions separately and deduce equality.
  apply Set.Subset.antisymm
  · -- `closure A ⊆ closure (interior A)`
    have h₁ : (closure A : Set X) ⊆ closure (interior (closure (interior A))) :=
      closure_mono h
    have h₂ :
        (closure (interior (closure (interior A))) : Set X) ⊆
          closure (closure (interior A)) :=
      closure_mono (interior_subset : interior (closure (interior A)) ⊆ closure (interior A))
    intro x hx
    have hx₁ := h₁ hx
    have hx₂ := h₂ hx₁
    simpa [closure_closure] using hx₂
  · -- `closure (interior A) ⊆ closure A`
    exact closure_mono (interior_subset : interior A ⊆ A)

theorem P1_empty {X : Type*} [TopologicalSpace X] : P1 (∅ : Set X) := by
  exact Set.empty_subset _

theorem P2_univ {X : Type*} [TopologicalSpace X] : P2 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P3 A) (hB : P3 B) : P3 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hAx =>
      have hxA : x ∈ interior (closure A) := hA hAx
      have h_subset :
          (interior (closure A) : Set X) ⊆ interior (closure (A ∪ B)) :=
        interior_mono
          (closure_mono
            (by
              simpa using (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)))
      exact h_subset hxA
  | inr hBx =>
      have hxB : x ∈ interior (closure B) := hB hBx
      have h_subset :
          (interior (closure B) : Set X) ⊆ interior (closure (A ∪ B)) :=
        interior_mono
          (closure_mono
            (by
              simpa using (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)))
      exact h_subset hxB

theorem P1_open {X : Type*} [TopologicalSpace X] {A : Set X} (h_open : IsOpen A) : P1 A := by
  exact P1_of_P2 (P2_open h_open)

theorem P3_univ {X : Type*} [TopologicalSpace X] : P3 (Set.univ : Set X) := by
  intro x hx
  simpa [closure_univ, interior_univ] using hx

theorem P2_empty {X : Type*} [TopologicalSpace X] : P2 (∅ : Set X) := by
  exact Set.empty_subset _

theorem P3_empty {X : Type*} [TopologicalSpace X] : P3 (∅ : Set X) := by
  exact Set.empty_subset _

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P3 (interior A) := by
  intro x hx
  exact mem_interior.mpr ⟨interior A, subset_closure, isOpen_interior, hx⟩

theorem P3_exists_subset_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P3 A) : ∃ U, IsOpen U ∧ A ⊆ U ∧ closure U ⊆ closure A := by
  refine ⟨interior (closure A), isOpen_interior, hA, ?_⟩
  have h_subset :
      (closure (interior (closure A)) : Set X) ⊆ closure (closure A) :=
    closure_mono (interior_subset : interior (closure A) ⊆ closure A)
  simpa [closure_closure] using h_subset

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {ℬ : Set (Set X)} (h : ∀ A, A ∈ ℬ → P1 A) : P1 (⋃₀ ℬ) := by
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hAx⟩
  have hPA : P1 A := h A hA_mem
  have hx_cl : x ∈ closure (interior A) := hPA hAx
  have h_subset : (closure (interior A) : Set X) ⊆ closure (interior (⋃₀ ℬ)) := by
    exact closure_mono (interior_mono (Set.subset_sUnion_of_mem hA_mem))
  exact h_subset hx_cl

theorem closure_eq_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P1 A) : closure A = closure (interior A) := by
  apply Set.Subset.antisymm
  ·
    have h₁ : (closure A : Set X) ⊆ closure (closure (interior A)) := closure_mono h
    simpa [closure_closure] using h₁
  ·
    exact closure_mono (interior_subset : interior A ⊆ A)

theorem P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (interior A) := by
  intro x hx
  simpa [interior_interior] using (subset_closure hx)

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {ℬ : Set (Set X)} (h : ∀ A, A ∈ ℬ → P2 A) : P2 (⋃₀ ℬ) := by
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hAx⟩
  have hPA : P2 A := h A hA_mem
  have hxA : x ∈ interior (closure (interior A)) := hPA hAx
  have h_subset :
      (interior (closure (interior A)) : Set X) ⊆
        interior (closure (interior (⋃₀ ℬ))) :=
    interior_mono
      (closure_mono
        (interior_mono
          (Set.subset_sUnion_of_mem hA_mem)))
  exact h_subset hxA

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {ℬ : Set (Set X)} (h : ∀ A, A ∈ ℬ → P3 A) : P3 (⋃₀ ℬ) := by
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hPA : P3 A := h A hA_mem
  have hx_int : x ∈ interior (closure A) := hPA hxA
  have h_subset :
      interior (closure A) ⊆ interior (closure (⋃₀ ℬ)) :=
    interior_mono
      (closure_mono
        (Set.subset_sUnion_of_mem hA_mem))
  exact h_subset hx_int

theorem P3_dense {X : Type*} [TopologicalSpace X] {A : Set X} (h : P3 A) : closure A = closure (interior (closure A)) := by
  apply Set.Subset.antisymm
  ·
    exact closure_mono (h : (A : Set X) ⊆ interior (closure A))
  ·
    have : (closure (interior (closure A)) : Set X) ⊆ closure A :=
      calc
        closure (interior (closure A)) ⊆ closure (closure A) :=
          closure_mono (interior_subset : interior (closure A) ⊆ closure A)
        _ = closure A := by simpa [closure_closure]
    exact this

theorem P2_iterate {X : Type*} [TopologicalSpace X] {A : Set X} : P2 (interior (closure (interior A))) := by
  simpa using
    (P2_open (A := interior (closure (interior A))) isOpen_interior)

theorem P3_pointwise {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P3 A) : ∀ x ∈ A, ∃ U, IsOpen U ∧ x ∈ U ∧ closure U ⊆ closure A := by
  intro x hx
  have hx_int : x ∈ interior (closure A) := hA hx
  rcases mem_interior.1 hx_int with ⟨U, hU_sub, hU_open, hxU⟩
  have h_closure_subset : (closure U : Set X) ⊆ closure A := by
    have h1 : (closure U : Set X) ⊆ closure (closure A) := closure_mono hU_sub
    simpa [closure_closure] using h1
  exact ⟨U, hU_open, hxU, h_closure_subset⟩

theorem P2_to_iterated_closure {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : A ⊆ closure (interior (closure (interior A))) := by
  exact subset_trans hA
    (subset_closure :
      (interior (closure (interior A)) : Set X) ⊆
        closure (interior (closure (interior A))))

theorem open_imp_P1_P2_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (h_open : IsOpen A) : P1 A ∧ P2 A ∧ P3 A := by
  exact ⟨P1_open (A := A) h_open, P2_open (A := A) h_open, P3_open (A := A) h_open⟩

theorem clopen_P1_iff_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hcl : IsClosed A) (hop : IsOpen A) : P1 A ↔ P2 A := by
  constructor
  · intro _hP1
    exact P2_open (A := A) hop
  · intro hP2
    exact P1_of_P2 (A := A) hP2

theorem P1_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (closure (interior A)) := by
  intro x hx
  have h_subset :
      (closure (interior A) : Set X) ⊆
        closure (interior (closure (interior A))) := by
    -- First, show `interior A ⊆ interior (closure (interior A))`
    have h_inner :
        (interior A : Set X) ⊆ interior (closure (interior A)) := by
      exact interior_maximal
        (subset_closure :
          (interior A : Set X) ⊆ closure (interior A))
        isOpen_interior
    -- Then, take closures on both sides
    exact closure_mono h_inner
  exact h_subset hx

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (h_dense : closure A = Set.univ) : P3 A := by
  intro x hx
  simpa [h_dense, interior_univ] using (Set.mem_univ x)

theorem P1_iff_closure_eq_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ closure A = closure (interior A) := by
  constructor
  · intro h
    exact closure_eq_of_P1 h
  · intro h_eq
    intro x hx
    have hx_closure : (x : X) ∈ closure A := subset_closure hx
    simpa [h_eq] using hx_closure

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h_dense : closure (interior A) = Set.univ) : P2 A := by
  intro x hx
  simpa [h_dense, interior_univ] using (Set.mem_univ x)

theorem interior_subset_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : interior A ⊆ interior (closure (interior A)) := by
  exact interior_subset.trans h

theorem P3_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} (h : ∀ i, P3 (A i)) : P3 (⋃ i, A i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  have hPi : P3 (A i) := h i
  have hx_int : x ∈ interior (closure (A i)) := hPi hxi
  have h_subset :
      (interior (closure (A i)) : Set X) ⊆ interior (closure (⋃ j, A j)) := by
    have subsetAi : (A i : Set X) ⊆ ⋃ j, A j := by
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact interior_mono (closure_mono subsetAi)
  exact h_subset hx_int

theorem P2_image_of_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {A : Set X} (hA : P2 A) : P2 (e '' A) := by
  -- First, rewrite what we have to prove.
  -- We must show `e '' A ⊆ interior (closure (interior (e '' A)))`.
  intro y hy
  -- Obtain a preimage point in `A`.
  rcases hy with ⟨x, hxA, rfl⟩
  -- Use `hA` to know that `x` already satisfies `P2`.
  have hx : x ∈ interior (closure (interior A)) := hA hxA
  -- Choose an open neighbourhood of `x` contained in `closure (interior A)`.
  rcases mem_interior.1 hx with ⟨U, hU_sub, hU_open, hxU⟩
  -- The image of an open set by a homeomorphism is open.
  have hU_im_open : IsOpen (e '' U) := (e.isOpenMap _ hU_open)
  -- `e x` is in that image.
  have hxy : (e x) ∈ e '' U := ⟨x, hxU, rfl⟩
  -- We show that this whole image is contained in the required closed set.
  have h_subset :
      (e '' U : Set Y) ⊆ closure (interior (e '' A)) := by
    -- Take an arbitrary point in `e '' U`.
    intro z hz
    rcases hz with ⟨u, huU, rfl⟩
    -- We will prove `e u` is in the closure of `interior (e '' A)`.
    have hu_cl : (u : X) ∈ closure (interior A) := hU_sub huU
    -- Use the neighbourhood characterisation of closure.
    have h_mem_cl :
        (∀ V : Set Y, IsOpen V → e u ∈ V → (V ∩ interior (e '' A)).Nonempty) := by
      intro V hV_open hV_mem
      -- Pull `V` back to an open set in `X`.
      have hV_pre_open : IsOpen (e ⁻¹' V) := hV_open.preimage e.continuous
      have hV_pre_mem : u ∈ e ⁻¹' V := hV_mem
      -- By closure, the preimage intersects `interior A`.
      have h_nonempty :=
        ((mem_closure_iff).1 hu_cl) (e ⁻¹' V) hV_pre_open hV_pre_mem
      rcases h_nonempty with ⟨w, hw_pre, hw_int⟩
      -- `w ∈ interior A`, hence `e w ∈ e '' interior A`.
      have h_image_mem : (e w) ∈ e '' interior A := ⟨w, hw_int, rfl⟩
      -- The image of an open set is open; it is contained in `e '' A`,
      -- hence in its interior.
      have h_img_open : IsOpen (e '' interior A) :=
        (e.isOpenMap _ isOpen_interior)
      have h_img_subset : (e '' interior A : Set Y) ⊆ e '' A := by
        intro y hy
        rcases hy with ⟨t, ht, rfl⟩
        exact ⟨t, interior_subset ht, rfl⟩
      have h_img_int :
          (e w) ∈ interior (e '' A) := by
        -- `e '' interior A` is an open neighbourhood contained in `e '' A`.
        exact
          mem_interior.2
            ⟨e '' interior A, h_img_subset, h_img_open, h_image_mem⟩
      -- Finally, build the required non‐empty intersection.
      exact ⟨e w, by
        refine And.intro ?_ h_img_int
        simpa using hw_pre⟩
    -- Convert the neighbourhood criterion into the membership in the closure.
    exact (mem_closure_iff).2 h_mem_cl
  -- We have an open neighbourhood of `e x` contained in the desired closed set,
  -- hence `e x` belongs to the interior of that closed set.
  exact
    mem_interior.2
      ⟨e '' U, h_subset, hU_im_open, hxy⟩

theorem P1_closed_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (h3 : P3 A) (hcl : IsClosed A) : P1 A := by
  intro x hx
  have hx_int : x ∈ interior A := by
    have hx' : x ∈ interior (closure A) := h3 hx
    simpa [hcl.closure_eq] using hx'
  exact subset_closure hx_int

theorem P1_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : P1 A := by
  intro x hx
  classical
  -- Since `X` is a subsingleton and `A` is non-empty, we have `A = univ`.
  have hAu : (A : Set X) = (Set.univ : Set X) := by
    ext y
    constructor
    · intro _; simp
    · intro _; 
      have : y = x := Subsingleton.elim y x
      simpa [this] using hx
  -- Hence `interior A = univ`.
  have hInt : interior A = (Set.univ : Set X) := by
    simpa [hAu, interior_univ]
  -- Therefore every point of `A` belongs to `closure (interior A)`.
  simpa [hInt, closure_univ] using (Set.mem_univ x)

theorem P2_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} (h : ∀ i, P2 (A i)) : P2 (⋃ i, A i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  have hPi : P2 (A i) := h i
  have hx_int : x ∈ interior (closure (interior (A i))) := hPi hxi
  have h_subset :
      (interior (closure (interior (A i))) : Set X) ⊆
        interior (closure (interior (⋃ j, A j))) := by
    have subsetAi : (A i : Set X) ⊆ ⋃ j, A j := by
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact interior_mono (closure_mono (interior_mono subsetAi))
  exact h_subset hx_int

theorem P1_univ {X : Type*} [TopologicalSpace X] : P1 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P3_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P3 A) (hB : P3 B) : P3 (A ×ˢ B) := by
  intro p hp
  -- Decompose the point `p` into its two coordinates.
  rcases p with ⟨x, y⟩
  -- Extract componentwise membership from `hp`.
  have hxA : x ∈ A := hp.1
  have hyB : y ∈ B := hp.2
  -- Apply the `P3` hypotheses to each component.
  have hx_int : x ∈ interior (closure A) := hA hxA
  have hy_int : y ∈ interior (closure B) := hB hyB
  -- Choose open neighbourhoods of `x` and `y` contained in the respective closures.
  rcases mem_interior.1 hx_int with ⟨U, hU_sub, hU_open, hxU⟩
  rcases mem_interior.1 hy_int with ⟨V, hV_sub, hV_open, hyV⟩
  -- The product of these neighbourhoods is an open neighbourhood of `(x, y)`.
  have hUV_open : IsOpen (U ×ˢ V) := hU_open.prod hV_open
  have hpUV : ((x, y) : X × Y) ∈ U ×ˢ V := by
    exact And.intro hxU hyV
  -- Show that this neighbourhood is contained in `closure (A ×ˢ B)`.
  have hUV_sub : (U ×ˢ V : Set (X × Y)) ⊆ closure (A ×ˢ B) := by
    intro z hz
    -- First, it is contained in `closure A ×ˢ closure B`.
    have hz_prod : z ∈ closure A ×ˢ closure B :=
      (Set.prod_mono hU_sub hV_sub) hz
    -- Identify this product with the closure of the product.
    simpa [closure_prod_eq] using hz_prod
  -- Conclude that `(x, y)` belongs to the required interior.
  exact
    mem_interior.2 ⟨U ×ˢ V, hUV_sub, hUV_open, hpUV⟩

theorem P2_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P2 A) (hB : P2 B) : P2 (A ×ˢ B) := by
  intro p hp
  rcases p with ⟨x, y⟩
  have hxA : x ∈ A := hp.1
  have hyB : y ∈ B := hp.2
  -- points are in the `P2` interiors
  have hx_int : x ∈ interior (closure (interior A)) := hA hxA
  have hy_int : y ∈ interior (closure (interior B)) := hB hyB
  -- choose open neighbourhoods
  rcases mem_interior.1 hx_int with ⟨U, hU_sub, hU_open, hxU⟩
  rcases mem_interior.1 hy_int with ⟨V, hV_sub, hV_open, hyV⟩
  -- open neighbourhood in the product
  have hUV_open : IsOpen (U ×ˢ V) := hU_open.prod hV_open
  have hpUV : ((x, y) : X × Y) ∈ U ×ˢ V := And.intro hxU hyV
  -- show the neighbourhood is contained in the required set
  have hUV_sub : (U ×ˢ V : Set (X × Y)) ⊆ closure (interior (A ×ˢ B)) := by
    intro z hz
    -- first, place `z` in the product of closures
    have hz_prod : z ∈ closure (interior A) ×ˢ closure (interior B) :=
      (Set.prod_mono hU_sub hV_sub) hz
    -- rewrite via `closure_prod_eq`
    have hz_cl₁ : z ∈ closure (interior A ×ˢ interior B) := by
      simpa [closure_prod_eq] using hz_prod
    -- `interior A × interior B` is an open subset of `A × B`
    have h_inner_subset :
        (interior A ×ˢ interior B : Set (X × Y)) ⊆ interior (A ×ˢ B) := by
      intro w hw
      have h_open : IsOpen (interior A ×ˢ interior B) :=
        isOpen_interior.prod isOpen_interior
      have h_sub : (interior A ×ˢ interior B : Set (X × Y)) ⊆ A ×ˢ B :=
        Set.prod_mono interior_subset interior_subset
      exact mem_interior.2 ⟨_, h_sub, h_open, hw⟩
    have h_closure_subset :
        (closure (interior A ×ˢ interior B) : Set (X × Y)) ⊆
          closure (interior (A ×ˢ B)) :=
      closure_mono h_inner_subset
    exact h_closure_subset hz_cl₁
  -- conclude
  exact mem_interior.2 ⟨U ×ˢ V, hUV_sub, hUV_open, hpUV⟩

theorem P3_image_of_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {A : Set X} (h : P3 A) : P3 (e '' A) := by
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` is in the interior of the closure of `A`
  have hx_int : x ∈ interior (closure A) := h hxA
  rcases mem_interior.1 hx_int with ⟨U, hU_sub, hU_open, hxU⟩
  -- The image of `U` is an open neighbourhood of `e x`
  have hV_open : IsOpen (e '' U) := by
    -- identify `e '' U` with a preimage under `e.symm`
    have h_eq : (e '' U : Set Y) = e.symm ⁻¹' U := by
      ext y
      constructor
      · intro hy
        rcases hy with ⟨u, huU, rfl⟩
        simpa using huU
      · intro hy
        exact ⟨e.symm y, hy, by simp⟩
    have h_pre : IsOpen (e.symm ⁻¹' U) := hU_open.preimage e.symm.continuous
    simpa [h_eq] using h_pre
  -- this image is contained in the desired closure
  have hV_sub : (e '' U : Set Y) ⊆ closure (e '' A) := by
    intro z hz
    rcases hz with ⟨u, huU, rfl⟩
    have hu_cl : (u : X) ∈ closure A := hU_sub huU
    -- prove `e u` is in the closure of `e '' A`
    have : (e u) ∈ closure (e '' A) := by
      refine (mem_closure_iff).2 ?_
      intro V hV_open hVu
      -- pull `V` back via `e`
      have h_pre_open : IsOpen (e ⁻¹' V) := hV_open.preimage e.continuous
      have h_pre_mem : u ∈ e ⁻¹' V := hVu
      obtain ⟨w, hw_pre, hwA⟩ :=
        (mem_closure_iff).1 hu_cl (e ⁻¹' V) h_pre_open h_pre_mem
      refine ⟨e w, ?_⟩
      have hwV : e w ∈ V := by
        have : w ∈ e ⁻¹' V := hw_pre
        simpa [Set.mem_preimage] using this
      have hwImg : e w ∈ e '' A := ⟨w, hwA, rfl⟩
      exact And.intro hwV hwImg
    exact this
  have h_mem : (e x) ∈ e '' U := ⟨x, hxU, rfl⟩
  exact mem_interior.2 ⟨e '' U, hV_sub, hV_open, h_mem⟩

theorem closure_subset_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : closure (interior A) ⊆ closure A := by
  exact closure_mono (interior_subset : interior A ⊆ A)

theorem P1_dense_iff {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ closure A ⊆ closure (interior A) := by
  constructor
  · intro hP1
    -- From `A ⊆ closure (interior A)` we deduce the desired inclusion on closures.
    have : (closure A : Set X) ⊆ closure (closure (interior A)) :=
      closure_mono hP1
    simpa [closure_closure] using this
  · intro hsubset
    -- We show `A ⊆ closure (interior A)`
    intro x hx
    have hx_cl : (x : X) ∈ closure A := subset_closure hx
    exact hsubset hx_cl

theorem P2_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : P2 A := by
  intro x hx
  classical
  -- In a subsingleton type, a non‐empty set must be the whole space.
  have hAu : (A : Set X) = (Set.univ : Set X) := by
    ext y
    constructor
    · intro _; simp
    · intro _
      have : y = x := Subsingleton.elim y x
      simpa [this] using hx
  -- Therefore the target set is `univ`, so the conclusion is immediate.
  simpa [hAu, interior_univ, closure_univ] using (Set.mem_univ x)

theorem P1_image_of_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {A : Set X} (hA : P1 A) : P1 (e '' A) := by
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- use the `P1` hypothesis on `A`
  have hx_cl : x ∈ closure (interior A) := hA hxA
  -- we show `e x` is in the required closure
  have : (e x) ∈ closure (interior (e '' A)) := by
    -- neighbourhood characterisation of closure
    refine (mem_closure_iff).2 ?_
    intro V hV_open hV_mem
    -- pull `V` back to `X`
    have hW_open : IsOpen (e ⁻¹' V) := hV_open.preimage e.continuous
    have hW_mem : x ∈ e ⁻¹' V := by
      change e x ∈ V at hV_mem
      simpa [Set.mem_preimage] using hV_mem
    -- use that `x` is in the closure of `interior A`
    have h_nonempty :=
      (mem_closure_iff).1 hx_cl (e ⁻¹' V) hW_open hW_mem
    rcases h_nonempty with ⟨w, hwW, hw_intA⟩
    -- translate back to `Y`
    have hwV : e w ∈ V := by
      have : w ∈ e ⁻¹' V := hwW
      simpa [Set.mem_preimage] using this
    -- `e w` lies in the interior of `e '' A`
    have h_open_img : IsOpen (e '' interior A) :=
      (e.isOpenMap _ isOpen_interior)
    have h_img_subset : (e '' interior A : Set Y) ⊆ e '' A := by
      intro z hz
      rcases hz with ⟨u, hu, rfl⟩
      exact ⟨u, interior_subset hu, rfl⟩
    have hw_int : e w ∈ interior (e '' A) := by
      refine
        mem_interior.2
          ⟨e '' interior A, h_img_subset, h_open_img, ?_⟩
      exact ⟨w, hw_intA, rfl⟩
    exact ⟨e w, And.intro hwV hw_int⟩
  exact this

theorem P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = Set.univ) : P3 A := by
  intro x hx
  -- First, prove that `closure A = univ`.
  have h_closure_univ : (closure (A : Set X)) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · -- `closure A ⊆ univ`
      intro y hy
      simp
    · -- `univ ⊆ closure A`, obtained from the assumption
      have h_subset : (closure (interior A) : Set X) ⊆ closure A :=
        closure_mono (interior_subset : (interior A : Set X) ⊆ A)
      simpa [h] using h_subset
  -- Since `closure A = univ`, its interior is `univ`, hence the goal holds.
  simpa [h_closure_univ, interior_univ]

theorem closure_eq_univ_of_P1_dense {X : Type*} [TopologicalSpace X] {A : Set X} (h : P1 A) (h_dense : closure (interior A) = Set.univ) : closure A = Set.univ := by
  apply Set.Subset.antisymm
  · intro x _; simp
  ·
    have : (closure (interior A) : Set X) ⊆ closure A :=
      closure_mono (interior_subset : (interior A : Set X) ⊆ A)
    simpa [h_dense] using this

theorem P1_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P1 A) (hB : P1 B) : P1 (A ×ˢ B) := by
  intro p hp
  rcases p with ⟨x, y⟩
  -- `x` and `y` belong to `A` and `B`
  have hxA : x ∈ A := hp.1
  have hyB : y ∈ B := hp.2
  -- use the `P1` hypotheses
  have hx_cl : x ∈ closure (interior A) := hA hxA
  have hy_cl : y ∈ closure (interior B) := hB hyB
  -- `(x, y)` is in the closure of `interior A × interior B`
  have hxy_cl_prod :
      ((x, y) : X × Y) ∈ closure (interior A ×ˢ interior B) := by
    -- thanks to `closure_prod_eq`
    have : ((x, y) : X × Y) ∈ closure (interior A) ×ˢ closure (interior B) :=
      And.intro hx_cl hy_cl
    simpa [closure_prod_eq] using this
  -- relate the two closures
  have h_subset :
      (closure (interior A ×ˢ interior B) : Set (X × Y)) ⊆
        closure (interior (A ×ˢ B)) := by
    -- first, an inclusion at the level of interiors
    have h_inner_subset :
        (interior A ×ˢ interior B : Set (X × Y)) ⊆ interior (A ×ˢ B) := by
      intro w hw
      have h_open : IsOpen (interior A ×ˢ interior B) :=
        isOpen_interior.prod isOpen_interior
      have h_sub : (interior A ×ˢ interior B : Set (X × Y)) ⊆ A ×ˢ B :=
        Set.prod_mono interior_subset interior_subset
      exact mem_interior.2 ⟨_, h_sub, h_open, hw⟩
    -- take closures on both sides
    exact closure_mono h_inner_subset
  -- conclude that `(x, y)` is in the desired closure
  exact h_subset hxy_cl_prod

theorem P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P2 (interior A) := by
  -- Unfold the definition of `P2`
  dsimp [P2]
  -- Apply monotonicity of `interior` to `subset_closure`
  simpa [interior_interior] using
    interior_mono (subset_closure : (interior A : Set X) ⊆ closure (interior A))

theorem exists_open_closure_eq_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P3 A) : ∃ U, IsOpen U ∧ A ⊆ U ∧ closure U = closure A := by
  rcases P3_exists_subset_open (A := A) hA with ⟨U, hU_open, hAU, hUcl_sub⟩
  refine ⟨U, hU_open, hAU, ?_⟩
  have h₁ : (closure U : Set X) ⊆ closure A := hUcl_sub
  have h₂ : (closure A : Set X) ⊆ closure U := closure_mono hAU
  exact Set.Subset.antisymm h₁ h₂

theorem P1_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} (hA : P1 A) (hB : P1 B) (hC : P1 C) : P1 (A ∪ B ∪ C) := by
  have hAB : P1 (A ∪ B) := P1_union hA hB
  have hABC : P1 ((A ∪ B) ∪ C) := P1_union hAB hC
  simpa [Set.union_assoc] using hABC

theorem P1_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} (h : ∀ i, P1 (A i)) : P1 (⋃ i, A i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  have hPi : P1 (A i) := h i
  have hx_cl : x ∈ closure (interior (A i)) := hPi hxi
  have h_subset :
      (closure (interior (A i)) : Set X) ⊆ closure (interior (⋃ j, A j)) :=
    closure_mono (interior_mono (Set.subset_iUnion A i))
  exact h_subset hx_cl

theorem P3_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : P3 A := by
  intro x hx
  classical
  -- In a subsingleton space, any non-empty set is the whole space.
  have hAu : (A : Set X) = (Set.univ : Set X) := by
    ext y
    constructor
    · intro _; simp
    · intro _
      have hxy : y = x := Subsingleton.elim y x
      simpa [hxy] using hx
  -- Rewriting gives the desired membership.
  simpa [hAu, closure_univ, interior_univ]

theorem P3_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} (hA : P3 A) (hB : P3 B) (hC : P3 C) : P3 (A ∪ B ∪ C) := by
  have hAB : P3 (A ∪ B) := P3_union hA hB
  have hABC : P3 ((A ∪ B) ∪ C) := P3_union hAB hC
  simpa [Set.union_assoc] using hABC

theorem P2_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} (hA : P2 A) (hB : P2 B) (hC : P2 C) : P2 (A ∪ B ∪ C) := by
  have hAB : P2 (A ∪ B) := P2_union (A := A) (B := B) hA hB
  have hABC : P2 ((A ∪ B) ∪ C) := P2_union hAB hC
  simpa [Set.union_assoc] using hABC

theorem P1_iff_P2_for_open_sets {X : Type*} [TopologicalSpace X] {A : Set X} (hop : IsOpen A) : P1 A ↔ P2 A := by
  constructor
  · intro _hP1
    exact P2_open (A := A) hop
  · intro hP2
    exact P1_of_P2 (A := A) hP2

theorem P3_univ_iff_true {X : Type*} [TopologicalSpace X] : P3 (Set.univ : Set X) ↔ True := by
  constructor
  · intro _
    trivial
  · intro _
    exact P3_univ (X := X)

theorem P2_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : P2 A) (hB : P2 B) (hC : P2 C) : P2 (Set.prod (Set.prod A B) C) := by
  -- First, get the `P2` property for `A ×ˢ B`.
  have hAB : P2 (Set.prod A B) := P2_prod (A := A) (B := B) hA hB
  -- Then, combine it with `C` to obtain the desired result.
  have hABC : P2 (Set.prod (Set.prod A B) C) :=
    P2_prod (A := Set.prod A B) (B := C) hAB hC
  simpa using hABC

theorem exists_open_dense_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : ∃ U, IsOpen U ∧ U ⊆ A ∧ closure U = closure (interior A) := by
  refine ⟨interior A, isOpen_interior, interior_subset, ?_⟩
  rfl

theorem P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h : P1 A) : P1 (closure A) := by
  intro x hx
  -- Step 1 : move from `x ∈ closure A` to `x ∈ closure (interior A)`.
  have hx₁ : (x : X) ∈ closure (interior A) := by
    -- `closure A ⊆ closure (closure (interior A))` thanks to `h`.
    have h₁ : (x : X) ∈ closure (closure (interior A)) :=
      (closure_mono h) hx
    -- Remove the superfluous `closure`.
    simpa [closure_closure] using h₁
  -- Step 2 : `closure (interior A) ⊆ closure (interior (closure A))`.
  have h_subset :
      (closure (interior A) : Set X) ⊆ closure (interior (closure A)) := by
    have h_inner : (interior A : Set X) ⊆ interior (closure A) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    exact closure_mono h_inner
  -- Finish.
  exact h_subset hx₁

theorem P2_of_P3_and_closed {X : Type*} [TopologicalSpace X] {A : Set X} (h3 : P3 A) (h_closed : IsClosed A) : P2 A := by
  intro x hx
  -- First, use `h3` to place `x` in `interior (closure A)`.
  have hx_int_closure : x ∈ interior (closure A) := h3 hx
  -- Since `A` is closed, `closure A = A`.
  have h_closure_eq : closure A = A := h_closed.closure_eq
  -- Hence `x ∈ interior A`.
  have hx_int : x ∈ interior A := by
    simpa [h_closure_eq] using hx_int_closure
  -- `interior A` is contained in `interior (closure (interior A))`.
  have h_subset : (interior A : Set X) ⊆ interior (closure (interior A)) :=
    interior_maximal (subset_closure : (interior A : Set X) ⊆ closure (interior A))
      isOpen_interior
  -- Conclude the desired membership.
  exact h_subset hx_int

theorem closure_eq_interior_closure_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : closure (interior (closure A)) = closure A := by
  simpa using (P3_dense (A := A) (P2_subset_P3 (A := A) hA)).symm

theorem exists_open_dense_subset_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : ∃ U, IsOpen U ∧ closure U = closure A := by
  refine ⟨interior A, isOpen_interior, ?_⟩
  simpa using (closure_eq_of_P1 (A := A) hA).symm

theorem P2_closed_iff_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X} (hcl : IsClosed A) : P2 A ↔ interior A = A := by
  constructor
  · intro hP2
    apply Set.Subset.antisymm
    · exact interior_subset
    · intro x hxA
      have hx_int_cl : x ∈ interior (closure (interior A)) := hP2 hxA
      rcases mem_interior.1 hx_int_cl with ⟨U, hU_sub, hU_open, hxU⟩
      have h_closure_subset : (closure (interior A) : Set X) ⊆ A := by
        have : (closure (interior A) : Set X) ⊆ closure A :=
          closure_mono (interior_subset : (interior A : Set X) ⊆ A)
        simpa [hcl.closure_eq] using this
      have hU_subA : (U : Set X) ⊆ A := hU_sub.trans h_closure_subset
      exact mem_interior.2 ⟨U, hU_subA, hU_open, hxU⟩
  · intro h_int_eq
    intro x hxA
    have hx_int : x ∈ interior A := by
      simpa [h_int_eq] using hxA
    have h_subset :
        (interior A : Set X) ⊆ interior (closure (interior A)) :=
      interior_maximal
        (subset_closure : (interior A : Set X) ⊆ closure (interior A))
        isOpen_interior
    exact h_subset hx_int

theorem P2_iff_P3_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P2 A ↔ P3 A := by
  constructor
  · intro hP2
    exact P2_subset_P3 (A := A) hP2
  · intro hP3
    exact P2_of_P3_and_closed (A := A) hP3 hA

theorem P1_Union_closures {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} (h : ∀ i, P1 (A i)) : P1 (⋃ i, closure (A i)) := by
  intro x hx
  -- pick the index witnessing the union
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- `P1 (A i)` yields `closure (A i) ⊆ closure (interior (A i))`
  have h_closure_subset :
      (closure (A i) : Set X) ⊆ closure (interior (A i)) :=
    (P1_dense_iff (X := X) (A := A i)).1 (h i)
  have hx₁ : x ∈ closure (interior (A i)) := h_closure_subset hx_i
  -- show that `interior (A i)` is contained in the interior of the big union
  have h_int_subset_int :
      (interior (A i) : Set X) ⊆ interior (⋃ j, closure (A j)) := by
    intro y hy
    rcases mem_interior.1 hy with ⟨U, hU_sub, hU_open, hyU⟩
    have hU_sub' : (U : Set X) ⊆ ⋃ j, closure (A j) := by
      intro z hz
      have hzAi : (z : X) ∈ A i := hU_sub hz
      have hz_cl : (z : X) ∈ closure (A i) := subset_closure hzAi
      exact Set.mem_iUnion.2 ⟨i, hz_cl⟩
    exact mem_interior.2 ⟨U, hU_sub', hU_open, hyU⟩
  -- take closures on both sides
  have h_subset :
      (closure (interior (A i)) : Set X) ⊆
        closure (interior (⋃ j, closure (A j))) :=
    closure_mono h_int_subset_int
  exact h_subset hx₁

theorem exists_compact_subset_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : ∃ K, IsCompact K ∧ K ⊆ A := by
  refine ⟨(∅ : Set X), isCompact_empty, ?_⟩
  exact Set.empty_subset _

theorem P3_iff_dense_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P3 A ↔ closure A = closure (interior A) := by
  constructor
  · intro _hP3
    simpa [hA.interior_eq]
  · intro _hEq
    exact P3_open (A := A) hA

theorem P3_closed_iff_eq_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : (P3 A) ↔ interior (closure A) = A := by
  -- Since `A` is closed, its closure is itself.
  have hcl : closure (A : Set X) = A := hA.closure_eq
  -- `P3 A` is equivalent to `P2 A` for closed sets.
  have hP3_P2 : (P3 A) ↔ (P2 A) :=
    (P2_iff_P3_of_closed (A := A) hA).symm
  -- For a closed set, `P2 A` is equivalent to `interior A = A`.
  have hP2_int : (P2 A) ↔ interior A = A :=
    P2_closed_iff_interior_eq (A := A) hA
  -- Combine the two equivalences.
  have hP3_int : (P3 A) ↔ interior A = A :=
    hP3_P2.trans hP2_int
  -- Rewrite using `hcl` to obtain the required statement.
  simpa [hcl] using hP3_int

theorem P3_iff_P2_of_dense_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h_dense : closure (interior A) = closure A) : P3 A ↔ P2 A := by
  have h_int : interior (closure (interior A)) = interior (closure A) := by
    simpa [h_dense]
  constructor
  · intro hP3
    intro x hx
    have hx_int : x ∈ interior (closure A) := hP3 hx
    simpa [h_int] using hx_int
  · intro hP2
    exact P2_subset_P3 (A := A) hP2

theorem P1_iff_P3_for_open_sets {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P1 A ↔ P3 A := by
  constructor
  · intro _
    exact P3_open (A := A) hA
  · intro _
    exact P1_open (A := A) hA

theorem P1_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : P1 A) (hB : P1 B) (hC : P1 C) : P1 (Set.prod (Set.prod A B) C) := by
  -- First obtain `P1` for the product `A ×ˢ B`
  have hAB : P1 (Set.prod A B) := P1_prod (A := A) (B := B) hA hB
  -- Then combine this with `C`
  have hABC : P1 (Set.prod (Set.prod A B) C) :=
    P1_prod (A := Set.prod A B) (B := C) hAB hC
  simpa using hABC

theorem P3_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : P3 A) (hB : P3 B) (hC : P3 C) : P3 (Set.prod (Set.prod A B) C) := by
  -- First obtain `P3` for the product `A ×ˢ B`
  have hAB : P3 (Set.prod A B) := P3_prod (A := A) (B := B) hA hB
  -- Then combine this with `C`
  have hABC : P3 (Set.prod (Set.prod A B) C) :=
    P3_prod (A := Set.prod A B) (B := C) hAB hC
  simpa using hABC

theorem exists_open_dense_subset_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P3 A) : ∃ U, IsOpen U ∧ A ⊆ U ∧ closure U = closure (interior (closure A)) := by
  refine ⟨interior (closure A), isOpen_interior, hA, rfl⟩

theorem P1_from_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : P1 (closure A) := by
  intro x hx_cl
  -- Step 1: use `hA : P2 A` to reach the intermediate closure
  have hx₁ : x ∈ closure (interior (closure (interior A))) := by
    have h_subset : (closure A : Set X) ⊆ closure (interior (closure (interior A))) :=
      closure_mono (hA : (A : Set X) ⊆ interior (closure (interior A)))
    exact h_subset hx_cl
  -- Step 2: compare the two target closures
  have h_subset' :
      (closure (interior (closure (interior A))) : Set X) ⊆
        closure (interior (closure A)) := by
    have h_inner :
        (interior (closure (interior A)) : Set X) ⊆ interior (closure A) := by
      have h_cl :
          (closure (interior A) : Set X) ⊆ closure A :=
        closure_mono (interior_subset : (interior A : Set X) ⊆ A)
      exact interior_mono h_cl
    exact closure_mono h_inner
  exact h_subset' hx₁

theorem closure_eq_iterated_interior_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : closure A = closure (interior (closure (interior A))) := by
  -- Step 1: `closure A = closure (interior A)` from `P1`.
  have h₁ : closure (A : Set X) = closure (interior A) :=
    closure_eq_of_P1 (A := A) hA
  -- Step 2: `closure (interior A)` equals the required iterated closure.
  have h₂ : closure (interior A) = closure (interior (closure (interior A))) := by
    -- `interior A` satisfies `P2`.
    have hP2 : P2 (interior A) := P2_interior (A := A)
    -- Use the equality given by `P2`, reversing its orientation.
    simpa using
      (closure_eq_interior_closure_of_P2 (A := interior A) hP2).symm
  -- Combine the two equalities.
  simpa using h₁.trans h₂

theorem P1_antisymm {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P1 A) (hB : P1 B) (hAB : A ⊆ B) (hBA : B ⊆ A) : closure (interior A) = closure (interior B) := by
  have hEq : (A : Set X) = B := Set.Subset.antisymm hAB hBA
  simpa [hEq]

theorem P2_subset_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : A ⊆ interior (closure A) := by
  intro x hx
  -- Use the `P2` hypothesis to go one step up in the chain
  have hx₁ : x ∈ interior (closure (interior A)) := hA hx
  -- Relate the two interiors through monotonicity
  have h_subset :
      (interior (closure (interior A)) : Set X) ⊆ interior (closure A) :=
    interior_mono (closure_mono (interior_subset : (interior A : Set X) ⊆ A))
  exact h_subset hx₁

theorem P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hd : closure (interior A) = Set.univ) : P1 A := by
  intro x hx
  simpa [hd.symm] using (Set.mem_univ x)

theorem P3_union_Inf {X : Type*} [TopologicalSpace X] {ℬ : Set (Set X)} (h : ∀ A ∈ ℬ, P3 A) : P3 (⋂₀ ℬ ∪ ⋃₀ ℬ) := by
  intro x hx
  classical
  by_cases hne : (ℬ : Set (Set X)).Nonempty
  · -- The family `ℬ` is non‐empty.
    rcases hne with ⟨A₀, hA₀⟩
    -- First, build `P3 (⋃₀ ℬ)`.
    have hP3_sUnion : P3 (⋃₀ ℬ) := by
      intro y hy
      rcases Set.mem_sUnion.1 hy with ⟨A, hA_mem, hyA⟩
      have hPA : P3 A := h A hA_mem
      have hy_int : y ∈ interior (closure A) := hPA hyA
      have h_subset :
          (interior (closure A) : Set X) ⊆ interior (closure (⋃₀ ℬ)) := by
        have h_cl_sub :
            (closure A : Set X) ⊆ closure (⋃₀ ℬ) :=
          closure_mono (by
            intro z hz
            exact Set.mem_sUnion.2 ⟨A, hA_mem, hz⟩)
        exact interior_mono h_cl_sub
      exact h_subset hy_int
    -- Now split on whether `x` comes from the intersection or the union.
    cases hx with
    | inl hx_inter =>
        -- Case `x ∈ ⋂₀ ℬ`.
        have hxA₀ : x ∈ A₀ := (Set.mem_sInter.1 hx_inter) _ hA₀
        have hP3A₀ : P3 A₀ := h A₀ hA₀
        have hx_int : x ∈ interior (closure A₀) := hP3A₀ hxA₀
        have h_subset :
            (interior (closure A₀) : Set X) ⊆
              interior (closure (⋂₀ ℬ ∪ ⋃₀ ℬ)) := by
          -- `A₀ ⊆ ⋂₀ ℬ ∪ ⋃₀ ℬ`.
          have hA₀_sub : (A₀ : Set X) ⊆ ⋂₀ ℬ ∪ ⋃₀ ℬ := by
            intro z hz
            exact Or.inr (Set.mem_sUnion.2 ⟨A₀, hA₀, hz⟩)
          have h_cl_sub :
              (closure A₀ : Set X) ⊆ closure (⋂₀ ℬ ∪ ⋃₀ ℬ) :=
            closure_mono hA₀_sub
          exact interior_mono h_cl_sub
        exact h_subset hx_int
    | inr hx_union =>
        -- Case `x ∈ ⋃₀ ℬ`.
        have hx_int : x ∈ interior (closure (⋃₀ ℬ)) := hP3_sUnion hx_union
        have h_subset :
            (interior (closure (⋃₀ ℬ)) : Set X) ⊆
              interior (closure (⋂₀ ℬ ∪ ⋃₀ ℬ)) := by
          -- `⋃₀ ℬ ⊆ ⋂₀ ℬ ∪ ⋃₀ ℬ`.
          have h_subset_union :
              (⋃₀ ℬ : Set X) ⊆ ⋂₀ ℬ ∪ ⋃₀ ℬ := by
            intro z hz
            exact Or.inr hz
          have h_cl_sub :
              (closure (⋃₀ ℬ) : Set X) ⊆
                closure (⋂₀ ℬ ∪ ⋃₀ ℬ) :=
            closure_mono h_subset_union
          exact interior_mono h_cl_sub
        exact h_subset hx_int
  · -- The family `ℬ` is empty.
    have h_empty : (ℬ : Set (Set X)) = ∅ := by
      apply (Set.eq_empty_iff_forall_not_mem).2
      intro A hA
      exact (hne ⟨A, hA⟩).elim
    -- Then `⋂₀ ℬ ∪ ⋃₀ ℬ = univ`.
    have h_union :
        (⋂₀ ℬ ∪ ⋃₀ ℬ : Set X) = (Set.univ : Set X) := by
      simp [h_empty]
    -- The interior of the closure of `univ` is `univ`.
    have : x ∈ interior (closure (⋂₀ ℬ ∪ ⋃₀ ℬ : Set X)) := by
      simpa [h_union, closure_univ, interior_univ] using Set.mem_univ x
    exact this

theorem P2_open_iff_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A ↔ P3 A := by
  -- Since `A` is open, its interior is itself.
  have hInt : interior A = A := hA.interior_eq
  -- Consequently, the two closures that appear in the definitions coincide.
  have hCl : closure (interior A) = closure A := by
    simpa [hInt]
  constructor
  · intro hP2
    exact P2_subset_P3 (A := A) hP2
  · intro hP3
    intro x hxA
    -- From `P3` we get that `x` lies in `interior (closure A)`.
    have hx_int : x ∈ interior (closure A) := hP3 hxA
    -- Rewrite with `hCl` to obtain the required conclusion.
    simpa [hCl] using hx_int

theorem P3_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = Set.univ) : P3 (closure A) := by
  -- First, prove that `closure (interior (closure A)) = univ`.
  have h_dense' : closure (interior (closure (A : Set X))) = (Set.univ : Set X) := by
    -- `interior A ⊆ interior (closure A)`, hence the corresponding closures satisfy the same inclusion.
    have h_sub :
        (closure (interior A) : Set X) ⊆ closure (interior (closure A)) :=
      closure_mono
        (interior_mono (subset_closure : (A : Set X) ⊆ closure A))
    -- Replace `closure (interior A)` with `univ` using the hypothesis.
    have h_univ_sub : (Set.univ : Set X) ⊆ closure (interior (closure A)) := by
      simpa [h] using h_sub
    -- Use subset antisymmetry to get the equality.
    apply Set.Subset.antisymm
    · intro _ _
      simp
    · exact h_univ_sub
  -- Conclude with the lemma giving `P3` from the denseness of the interior.
  exact P3_of_dense_interior (A := closure A) h_dense'

theorem P2_singleton_of_discrete {X : Type*} [TopologicalSpace X] [DiscreteTopology X] {x : X} : P2 ({x} : Set X) := by
  intro y hy
  -- Reduce to the case `y = x`
  have hy_eq : y = x := by
    simpa using (Set.mem_singleton_iff.mp hy)
  -- `{x}` is open in a discrete topology, hence `interior {x} = {x}`
  have h_open : IsOpen ({x} : Set X) := isOpen_discrete _
  have h_int_eq : interior ({x} : Set X) = ({x} : Set X) := h_open.interior_eq
  -- Consequently, `{x} ⊆ closure (interior {x})`
  have h_subset : ({x} : Set X) ⊆ closure (interior ({x} : Set X)) := by
    have h : ({x} : Set X) ⊆ closure ({x} : Set X) := subset_closure
    simpa [h_int_eq] using h
  -- Using the open neighbourhood `{x}`, we put `x` in the required interior
  have hx_in : x ∈ interior (closure (interior ({x} : Set X))) := by
    have hx_mem : x ∈ ({x} : Set X) := by simp
    exact mem_interior.2 ⟨({x} : Set X), h_subset, h_open, hx_mem⟩
  simpa [hy_eq] using hx_in

theorem P2_dense_interior_union {X : Type*} [TopologicalSpace X] {A : Set X} (hd : closure (interior A) = Set.univ) : P2 (A ∪ interior A) := by
  -- `interior A` is contained in `A`, hence their union is just `A`.
  have h_union_eq : (A ∪ interior A : Set X) = A := by
    ext x
    constructor
    · intro hx
      cases hx with
      | inl hxA      => exact hxA
      | inr hxIntA   => exact interior_subset hxIntA
    · intro hxA
      exact Or.inl hxA
  -- From the density hypothesis we already have `P2 A`.
  have hP2 : P2 A := P2_of_dense_interior (A := A) hd
  -- Rewriting with the previous equality yields the desired statement.
  simpa [h_union_eq] using hP2

theorem P2_subset_closure_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : A ⊆ closure (interior (closure A)) := by
  intro x hxA
  -- Step 1: from `P2`, place `x` in `interior (closure (interior A))`.
  have hx₁ : x ∈ interior (closure (interior A)) := h hxA
  -- Step 2: the interior is contained in its own closure.
  have hx₂ : x ∈ closure (interior (closure (interior A))) :=
    subset_closure hx₁
  -- Step 3: compare the two closures.
  have h_subset :
      (closure (interior (closure (interior A))) : Set X) ⊆
        closure (interior (closure A)) := by
    -- First, relate the interiors.
    have h_inner :
        (interior (closure (interior A)) : Set X) ⊆
          interior (closure A) := by
      -- `closure (interior A) ⊆ closure A`
      have h_closure :
          (closure (interior A) : Set X) ⊆ closure A :=
        closure_mono (interior_subset : (interior A : Set X) ⊆ A)
      exact interior_mono h_closure
    -- Take closures of both sides.
    exact closure_mono h_inner
  -- Step 4: conclude.
  exact h_subset hx₂

theorem P2_union_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : P2 (A ∪ interior A) := by
  -- Since `interior A ⊆ A`, the union is just `A`.
  have hEq : (A ∪ interior A : Set X) = A := by
    ext x
    constructor
    · intro hx
      cases hx with
      | inl hA   => exact hA
      | inr hInt => exact interior_subset hInt
    · intro hx
      exact Or.inl hx
  simpa [hEq] using h

theorem P2_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : P2 A) : P2 (A ×ˢ (Set.univ : Set Y)) := by
  -- `P2` holds for `Set.univ`, by a previous lemma.
  have hUniv : P2 (Set.univ : Set Y) := P2_univ (X := Y)
  -- Apply the product lemma for `P2` and simplify.
  simpa using (P2_prod (A := A) (B := (Set.univ : Set Y)) hA hUniv)

theorem P3_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : P3 A) : P3 (A ×ˢ (Set.univ : Set Y)) := by
  -- `P3` holds for `Set.univ` in any topological space.
  have hUniv : P3 (Set.univ : Set Y) := P3_univ (X := Y)
  -- Apply the product lemma for `P3` and simplify.
  simpa using (P3_prod (A := A) (B := (Set.univ : Set Y)) hA hUniv)

theorem exists_closed_subset_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P3 A) : ∃ K, IsClosed K ∧ K ⊆ A ∧ P3 K := by
  refine ⟨(∅ : Set X), isClosed_empty, Set.empty_subset _, ?_⟩
  exact P3_empty (X := X)

theorem P1_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : P1 A) : P1 (A ×ˢ (Set.univ : Set Y)) := by
  have hUniv : P1 (Set.univ : Set Y) := P1_univ (X := Y)
  simpa using (P1_prod (A := A) (B := (Set.univ : Set Y)) hA hUniv)

theorem P1_of_closure_subset_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure A ⊆ interior A) : P1 A := by
  intro x hx
  have hx_cl : (x : X) ∈ closure A := subset_closure hx
  have hx_int : (x : X) ∈ interior A := h hx_cl
  exact subset_closure hx_int

theorem P2_bUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} (h : ∀ i, P2 (A i)) : P2 (⋃₀ {S | ∃ i, S = A i}) := by
  exact
    P2_sUnion (X := X) (ℬ := {S | ∃ i, S = A i})
      (by
        intro S hS
        rcases hS with ⟨i, rfl⟩
        exact h i)

theorem P1_dense_image_of_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {A : Set X} (hA : P1 A) : closure (e '' A) = closure (interior (e '' A)) := by
  have h : P1 (e '' A) := P1_image_of_homeomorph (e := e) (A := A) hA
  simpa using (closure_eq_of_P1 (A := e '' A) h)

theorem interior_closure_eq_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : interior (closure A) = interior (closure (interior A)) := by
  have hcl : closure (A : Set X) = closure (interior A) :=
    closure_eq_of_P2 (A := A) h
  simpa [hcl]

theorem interior_eq_self_of_P3_closed {X : Type*} [TopologicalSpace X] {A : Set X} (h3 : P3 A) (hcl : IsClosed A) : interior A = A := by
  -- `A` is closed, so its closure is itself.
  have h_cl : closure (A : Set X) = A := hcl.closure_eq
  -- From `P3_closed_iff_eq_interior_closure` we obtain `interior (closure A) = A`.
  have h_int_closure : interior (closure A) = A :=
    (P3_closed_iff_eq_interior_closure (A := A) hcl).1 h3
  -- Rewriting `closure A` with `A` gives the desired result.
  simpa [h_cl] using h_int_closure

theorem P1_pow {X : Type*} [TopologicalSpace X] {A : Set X} {n : ℕ} (hA : P1 A) : P1 ((fun x => x)^[n] '' A) := by
  -- The `n`-fold iterate of the identity map is the identity map.
  have h_iter : (Nat.iterate (fun x : X => x) n) = (fun x : X => x) := by
    funext x
    induction n with
    | zero      => rfl
    | succ n ih => simp [Nat.iterate, ih]
  -- Hence the image of `A` under this map is just `A` itself.
  have h_img : ((Nat.iterate (fun x : X => x) n) '' (A : Set X)) = A := by
    simpa [h_iter, Set.image_id]
  -- Rewriting with this equality, the goal reduces to `P1 A`.
  simpa [P1, h_img] using hA

theorem P2_iteration_fixed {X : Type*} [TopologicalSpace X] {A : Set X} : (Nat.iterate (fun S : Set X => interior (closure (interior S))) 3 A) ⊆ interior (closure (interior A)) := by
  -- Define the operator that is iterated.
  let f : Set X → Set X := fun S : Set X => interior (closure (interior S))

  -- Key lemma: a double application of `f` is contained in a single one.
  have hf_step : ∀ S : Set X, f (f S) ⊆ f S := by
    intro S
    dsimp [f]
    -- 1.  `interior (closure (interior S)) ⊆ closure (interior S)`
    have h₁ :
        (interior (closure (interior S)) : Set X) ⊆
          closure (interior S) :=
      interior_subset
    -- 2.  Take closures on both sides; rewrite `closure (closure _)`.
    have h₂ :
        (closure (interior (closure (interior S))) : Set X) ⊆
          closure (interior S) := by
      have h' :
          (closure (interior (closure (interior S))) : Set X) ⊆
            closure (closure (interior S)) :=
        closure_mono h₁
      simpa [closure_closure] using h'
    -- 3.  Take interiors once more to arrive at the desired inclusion.
    have h₃ :
        (interior (closure (interior (closure (interior S)))) : Set X) ⊆
          interior (closure (interior S)) :=
      interior_mono h₂
    -- The two sides are precisely `f (f S)` and `f S`.
    simpa [f] using h₃

  -- Apply the shrinking lemma twice to control the triple iterate.
  have h₁ : (Nat.iterate f 3 A) ⊆ f (f A) := by
    -- `Nat.iterate f 3 A` is definitionally `f (f (f A))`.
    simpa [Nat.iterate] using hf_step (f A)
  have h₂ : f (f A) ⊆ f A := hf_step A
  have h_final : (Nat.iterate f 3 A) ⊆ f A := h₁.trans h₂

  -- Rewrite `f A` to the required expression and finish.
  simpa [f] using h_final

theorem P2_union_complement {X : Type*} [TopologicalSpace X] {A : Set X} : P2 (A ∪ Aᶜ) := by
  simpa [Set.union_compl_self] using (P2_univ (X := X))

theorem P1_inter_complement {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (A ∩ Aᶜ) := by
  simpa [Set.inter_compl_self] using (P1_empty (X := X))

theorem P2_sigma {X : Type*} {Y : X → Type*} [∀ x, TopologicalSpace (Y x)] [TopologicalSpace (Σ x, Y x)] {A : Set (Σ x, Y x)} (h : ∀ x, P2 {p : Σ x, Y x | p.1 = x ∧ p ∈ A}) : P2 A := by
  intro p hpA
  -- `p` belongs to the fibre of `A` over `p.1`
  have hp_fibre :
      p ∈ {q : Σ x, Y x | q.1 = p.1 ∧ q ∈ (A : Set (Σ x, Y x))} := by
    exact And.intro rfl hpA
  -- Apply the hypothesis on that fibre
  have hp_in :
      p ∈ interior (closure (interior {q : Σ x, Y x | q.1 = p.1 ∧ q ∈ A})) :=
    (h (p.1)) hp_fibre
  -- The iterated interior of the fibre is contained in the one of `A`
  have h_subset :
      (interior (closure (interior {q : Σ x, Y x | q.1 = p.1 ∧ q ∈ A})) :
          Set (Σ x, Y x)) ⊆
        interior (closure (interior A)) := by
    -- first inclusion of sets
    have h_fibre_sub :
        ({q : Σ x, Y x | q.1 = p.1 ∧ q ∈ A} :
            Set (Σ x, Y x)) ⊆ A := by
      intro q hq
      exact hq.2
    have h_inner :
        (interior {q : Σ x, Y x | q.1 = p.1 ∧ q ∈ A} :
            Set (Σ x, Y x)) ⊆
          interior A :=
      interior_mono h_fibre_sub
    have h_closure :
        (closure (interior {q : Σ x, Y x | q.1 = p.1 ∧ q ∈ A}) :
            Set (Σ x, Y x)) ⊆
          closure (interior A) :=
      closure_mono h_inner
    exact interior_mono h_closure
  exact h_subset hp_in

theorem P3_iterate {X : Type*} [TopologicalSpace X] {A : Set X} (n : ℕ) (h : P3 A) : P3 ((fun x => x)^[n] '' A) := by
  -- The `n`-th iterate of the identity map is the identity itself.
  have h_iter : (Nat.iterate (fun x : X => x) n) = fun x : X => x := by
    funext x
    induction n with
    | zero      => rfl
    | succ n ih => simpa [Nat.iterate, ih]
  -- Hence the image of `A` under this map is just `A`.
  have h_img : (Nat.iterate (fun x : X => x) n) '' (A : Set X) = A := by
    simpa [h_iter, Set.image_id]
  -- Rewriting with this equality, the goal reduces to the given hypothesis.
  simpa [P3, h_img] using h

theorem P1_bUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} (H : ∀ i, P1 (A i)) : P1 (⋃₀ {S | ∃ i, S = A i}) := by
  simpa using
    (P1_sUnion (X := X) (ℬ := {S : Set X | ∃ i, S = A i})
      (by
        intro S hS
        rcases hS with ⟨i, rfl⟩
        exact H i))

theorem P2_union_closed_dense {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : IsClosed A) (hdB : closure (interior B) = Set.univ) : P2 (A ∪ B) := by
  intro x hx
  -- First, we show that the closure of the interior of the union is the whole
  -- space, using the density of `interior B`.
  have h_closure_eq : closure (interior (A ∪ B)) = (Set.univ : Set X) := by
    -- We prove the two inclusions separately.
    apply Set.Subset.antisymm
    · -- `closure (interior (A ∪ B)) ⊆ univ`
      intro y hy
      trivial
    · -- `univ ⊆ closure (interior (A ∪ B))`
      intro y hy
      -- `y` is in `closure (interior B)` because this set is `univ`.
      have h_in_closureB : (y : X) ∈ closure (interior B) := by
        simpa [hdB] using (Set.mem_univ y)
      -- `interior B ⊆ interior (A ∪ B)`, hence the same holds for closures.
      have h_subset :
          (closure (interior B) : Set X) ⊆
            closure (interior (A ∪ B)) :=
        closure_mono
          (interior_mono
            (by
              simpa using
                (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)))
      exact h_subset h_in_closureB
  -- Since this closure is `univ`, its interior is also `univ`, and the goal
  -- follows immediately.
  have : (x : X) ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_closure_eq, interior_univ] using this

theorem P2_exists_dense_subset {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : ∃ B, B ⊆ A ∧ closure (interior B) = closure (interior A) := by
  refine ⟨interior A, interior_subset, ?_⟩
  simpa [interior_interior]