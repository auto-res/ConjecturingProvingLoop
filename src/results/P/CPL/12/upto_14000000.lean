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
  intro hP2
  have h1 : interior (closure (interior A)) ⊆ interior (closure A) := by
    have hcl : closure (interior A) ⊆ closure A := by
      have : interior A ⊆ A := interior_subset
      exact closure_mono this
    exact interior_mono hcl
  exact Set.Subset.trans hP2 h1

theorem P1_univ {X : Type*} [TopologicalSpace X] : P1 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P3_empty {X : Type*} [TopologicalSpace X] : P3 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P2 A → P2 B → P2 (A ∪ B) := by
  intro hA hB
  -- We need to show `(A ∪ B) ⊆ interior (closure (interior (A ∪ B)))`
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x ∈ A`
      have hx' : x ∈ interior (closure (interior A)) := hA hxA
      -- `interior (closure (interior A)) ⊆ interior (closure (interior (A ∪ B)))`
      have hmono : interior (closure (interior A)) ⊆
          interior (closure (interior (A ∪ B))) := by
        have h₁ : interior A ⊆ interior (A ∪ B) :=
          interior_mono (Set.subset_union_left)
        have h₂ : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
          closure_mono h₁
        exact interior_mono h₂
      exact hmono hx'
  | inr hxB =>
      -- `x ∈ B`
      have hx' : x ∈ interior (closure (interior B)) := hB hxB
      -- `interior (closure (interior B)) ⊆ interior (closure (interior (A ∪ B)))`
      have hmono : interior (closure (interior B)) ⊆
          interior (closure (interior (A ∪ B))) := by
        have h₁ : interior B ⊆ interior (A ∪ B) :=
          interior_mono (Set.subset_union_right)
        have h₂ : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
          closure_mono h₁
        exact interior_mono h₂
      exact hmono hx'

theorem P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P2 (interior A) := by
  intro x hx
  have hsubset : interior A ⊆ interior (closure (interior A)) := by
    simpa [interior_interior] using
      (interior_mono (subset_closure : interior A ⊆ closure (interior A)))
  simpa [interior_interior] using hsubset hx

theorem P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (interior A) := by
  intro x hx
  simpa [interior_interior] using
    (subset_closure : (interior A) ⊆ closure (interior A)) hx

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P3 A → P3 B → P3 (A ∪ B) := by
  intro hA hB
  intro x hx
  cases hx with
  | inl hxA =>
      have hx' : x ∈ interior (closure A) := hA hxA
      have hmono : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        have hcl : closure A ⊆ closure (A ∪ B) :=
          closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
        exact interior_mono hcl
      exact hmono hx'
  | inr hxB =>
      have hx' : x ∈ interior (closure B) := hB hxB
      have hmono : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        have hcl : closure B ⊆ closure (A ∪ B) :=
          closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
        exact interior_mono hcl
      exact hmono hx'

theorem P2_empty {X : Type*} [TopologicalSpace X] : P2 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P1_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P1 A := by
  intro hP2
  exact Set.Subset.trans hP2 interior_subset

theorem P1_empty {X : Type*} [TopologicalSpace X] : P1 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P3_univ {X : Type*} [TopologicalSpace X] : P3 (Set.univ : Set X) := by
  intro x hx
  simpa [closure_univ, interior_univ] using hx

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P1 A → P1 B → P1 (A ∪ B) := by
  intro hA hB
  intro x hx
  cases hx with
  | inl hxA =>
      have hx' : x ∈ closure (interior A) := hA hxA
      have hmono : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        have hsubset : interior A ⊆ interior (A ∪ B) :=
          interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
        exact closure_mono hsubset
      exact hmono hx'
  | inr hxB =>
      have hx' : x ∈ closure (interior B) := hB hxB
      have hmono : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        have hsubset : interior B ⊆ interior (A ∪ B) :=
          interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
        exact closure_mono hsubset
      exact hmono hx'

theorem P1_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (closure (interior A)) := by
  intro x hx
  have hsubset : interior A ⊆ interior (closure (interior A)) := by
    simpa using
      interior_mono (subset_closure : interior A ⊆ closure (interior A))
  have hclosure :
      closure (interior A) ⊆ closure (interior (closure (interior A))) :=
    closure_mono hsubset
  exact hclosure hx

theorem P1_iff_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P1 A ↔ P3 A := by
  have hInt : interior A = A := hA.interior_eq
  constructor
  · intro _hP1
    intro x hx
    have hx_int : x ∈ interior A := by
      simpa [hInt] using hx
    have hsubset : interior A ⊆ interior (closure A) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    exact hsubset hx_int
  · intro _hP3
    intro x hx
    have hx_int : x ∈ interior A := by
      simpa [hInt] using hx
    exact (subset_closure : interior A ⊆ closure (interior A)) hx_int

theorem P2_iff_P3_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P2 A ↔ P3 A := by
  constructor
  · intro hP2
    exact P3_of_P2 hP2
  · intro hP3
    intro x hx
    -- First, show that x ∈ interior A (since A is closed and satisfies P3)
    have hx_int : x ∈ interior A := by
      have : x ∈ interior (closure A) := hP3 hx
      simpa [hA.closure_eq] using this
    -- Now use the monotonicity of interior/closure
    have hsubset : interior A ⊆ interior (closure (interior A)) := by
      simpa [interior_interior] using
        interior_mono (subset_closure : interior A ⊆ closure (interior A))
    exact hsubset hx_int

theorem P2_univ {X : Type*} [TopologicalSpace X] : P2 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → P2 A := by
  intro hA
  have hInt : interior A = A := hA.interior_eq
  intro x hx
  have hx_int : x ∈ interior A := by
    simpa [hInt] using hx
  have : x ∈ interior (closure A) :=
    (interior_mono (subset_closure : (A : Set X) ⊆ closure A)) hx_int
  simpa [hInt] using this

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {ℱ : Set (Set X)} : (∀ A, A ∈ ℱ → P1 A) → P1 (⋃₀ ℱ) := by
  intro hAll
  intro x hx
  rcases Set.mem_sUnion.mp hx with ⟨A, hA_mem, hxA⟩
  have hP1A : P1 A := hAll A hA_mem
  have hx' : x ∈ closure (interior A) := hP1A hxA
  have hsubset : closure (interior A) ⊆ closure (interior (⋃₀ ℱ)) := by
    have hInt : interior A ⊆ interior (⋃₀ ℱ) := by
      have hAsub : (A : Set X) ⊆ ⋃₀ ℱ := by
        intro y hy
        exact Set.mem_sUnion.mpr ⟨A, hA_mem, hy⟩
      exact interior_mono hAsub
    exact closure_mono hInt
  exact hsubset hx'

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P3 A → P3 (interior A) := by
  intro _hP3
  intro x hx
  have hsubset : (interior A : Set X) ⊆ interior (closure (interior A)) := by
    simpa using
      interior_mono (subset_closure : (interior A : Set X) ⊆ closure (interior A))
  exact hsubset hx

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {ℱ : Set (Set X)} : (∀ A, A ∈ ℱ → P2 A) → P2 (⋃₀ ℱ) := by
  intro hAll
  intro x hx
  rcases Set.mem_sUnion.mp hx with ⟨A, hA_mem, hxA⟩
  have hPA : P2 A := hAll A hA_mem
  have hx' : x ∈ interior (closure (interior A)) := hPA hxA
  have hsubset :
      interior (closure (interior A)) ⊆ interior (closure (interior (⋃₀ ℱ))) := by
    have hInt : interior A ⊆ interior (⋃₀ ℱ) := by
      have hAsub : (A : Set X) ⊆ ⋃₀ ℱ := by
        intro y hy
        exact Set.mem_sUnion.mpr ⟨A, hA_mem, hy⟩
      exact interior_mono hAsub
    have hcl : closure (interior A) ⊆ closure (interior (⋃₀ ℱ)) :=
      closure_mono hInt
    exact interior_mono hcl
  exact hsubset hx'

theorem P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → P3 A := by
  intro hA
  intro x hx
  have hx_int : x ∈ interior A := by
    simpa [hA.interior_eq] using hx
  have hsubset : interior A ⊆ interior (closure A) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  exact hsubset hx_int

namespace Topology

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {ℱ : Set (Set X)} : (∀ A, A ∈ ℱ → P3 A) → P3 (⋃₀ ℱ) := by
  intro hAll
  intro x hx
  rcases Set.mem_sUnion.mp hx with ⟨A, hA_mem, hxA⟩
  have hP3A : P3 A := hAll A hA_mem
  have hx' : x ∈ interior (closure A) := hP3A hxA
  have hsubset : interior (closure A) ⊆ interior (closure (⋃₀ ℱ)) := by
    have hcl : closure A ⊆ closure (⋃₀ ℱ) := by
      have hAsub : (A : Set X) ⊆ ⋃₀ ℱ := by
        intro y hy
        exact Set.mem_sUnion.mpr ⟨A, hA_mem, hy⟩
      exact closure_mono hAsub
    exact interior_mono hcl
  exact hsubset hx'

namespace Topology

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} : closure (interior A) = Set.univ → P2 A := by
  intro hDense
  intro x hx
  have h_univ : (x : X) ∈ (Set.univ : Set X) := by
    simp
  simpa [hDense, interior_univ] using h_univ

namespace Topology

theorem P3_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen (closure A) → P3 A := by
  intro hOpen
  intro x hx
  have hx_cl : x ∈ closure A := (subset_closure : (A : Set X) ⊆ closure A) hx
  simpa [hOpen.interior_eq] using hx_cl

namespace Topology

theorem P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} : closure (interior A) = Set.univ → P1 A := by
  intro hDense x _
  simpa [hDense] using (Set.mem_univ x)

theorem P3_iff_P1_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = Set.univ) : P3 A ↔ P1 A := by
  -- First, note that `closure A = univ`, since it contains `closure (interior A) = univ`.
  have hClosureA : (closure (A : Set X)) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · simp
    · simpa [h] using
        (closure_mono (interior_subset : (interior A : Set X) ⊆ A))
  -- Rewrite the two predicates with these equalities and finish by `simp`.
  unfold P3 P1
  simpa [h, hClosureA]

theorem P1_iUnion {X : Type*} {ι : Sort*} [TopologicalSpace X] {A : ι → Set X} : (∀ i, P1 (A i)) → P1 (Set.iUnion A) := by
  intro hAll
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
  have hP1 : P1 (A i) := hAll i
  have hx' : x ∈ closure (interior (A i)) := hP1 hxi
  have hsubset :
      closure (interior (A i)) ⊆ closure (interior (Set.iUnion A)) := by
    have hInt : interior (A i) ⊆ interior (Set.iUnion A) := by
      have hAi_sub : (A i : Set X) ⊆ Set.iUnion A := by
        exact Set.subset_iUnion _ _
      exact interior_mono hAi_sub
    exact closure_mono hInt
  exact hsubset hx'

theorem P2_univ_iff {X : Type*} [TopologicalSpace X] : P2 (Set.univ : Set X) ↔ True := by
  constructor
  · intro _
    trivial
  · intro _
    exact P2_univ

theorem P2_iUnion {X : Type*} {ι : Sort*} [TopologicalSpace X] {A : ι → Set X} : (∀ i, P2 (A i)) → P2 (Set.iUnion A) := by
  intro hAll
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxAi⟩
  have hP2 : P2 (A i) := hAll i
  have hx' : x ∈ interior (closure (interior (A i))) := hP2 hxAi
  have hsubset : interior (closure (interior (A i))) ⊆
      interior (closure (interior (Set.iUnion A))) := by
    have hInt : interior (A i) ⊆ interior (Set.iUnion A) := by
      have hAi_sub : (A i : Set X) ⊆ Set.iUnion A :=
        Set.subset_iUnion _ _
      exact interior_mono hAi_sub
    have hcl : closure (interior (A i)) ⊆ closure (interior (Set.iUnion A)) :=
      closure_mono hInt
    exact interior_mono hcl
  exact hsubset hx'

theorem P3_iUnion {X : Type*} {ι : Sort*} [TopologicalSpace X] {A : ι → Set X} : (∀ i, P3 (A i)) → P3 (Set.iUnion A) := by
  intro hAll
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxAi⟩
  have hP3 : P3 (A i) := hAll i
  have hx' : x ∈ interior (closure (A i)) := hP3 hxAi
  have hsubset : interior (closure (A i)) ⊆ interior (closure (Set.iUnion A)) := by
    have hcl : closure (A i) ⊆ closure (Set.iUnion A) := by
      have hAi_sub : (A i : Set X) ⊆ Set.iUnion A := Set.subset_iUnion _ _
      exact closure_mono hAi_sub
    exact interior_mono hcl
  exact hsubset hx'

theorem P1_iff_P2_of_clopen {X : Type*} [TopologicalSpace X] {A : Set X} (hA₁ : IsOpen A) (hA₂ : IsClosed A) : P1 A ↔ P2 A := by
  have hInt : interior (A : Set X) = A := hA₁.interior_eq
  have hP1_to_P2 : P1 A → P2 A := by
    intro _hP1
    intro x hx
    simpa [hInt, hA₂.closure_eq] using hx
  exact ⟨hP1_to_P2, P1_of_P2⟩

theorem P3_iff_P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P3 A ↔ P2 A := by
  have hInt : interior (A : Set X) = A := hA.interior_eq
  simpa [P2, P3, hInt]

theorem P1_iff_P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P1 A ↔ P2 A := by
  have hP1_to_P2 : P1 A → P2 A := by
    intro _hP1
    intro x hx
    -- Since `A` is open, `interior A = A`.
    have hx_int : x ∈ interior A := by
      simpa [hA.interior_eq] using hx
    -- Monotonicity: `interior A ⊆ interior (closure (interior A))`.
    have hsubset : interior A ⊆ interior (closure (interior A)) := by
      simpa [interior_interior] using
        interior_mono (subset_closure : interior A ⊆ closure (interior A))
    exact hsubset hx_int
  exact ⟨hP1_to_P2, P1_of_P2⟩

theorem P2_of_closed_complement {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → P2 (Aᶜ) := by
  intro hClosed
  simpa using P2_of_open (hClosed.isOpen_compl)

theorem P1_of_closure_interior_eq_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = closure A) : P1 A := by
  intro x hx
  simpa [h] using (subset_closure : (A : Set X) ⊆ closure A) hx

theorem P1_of_open {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → P1 A := by
  intro hA x hx
  simpa [hA.interior_eq] using (subset_closure hx : x ∈ closure A)

theorem P3_of_dense_closure {X : Type*} [TopologicalSpace X] {A : Set X} : closure A = Set.univ → P3 A := by
  intro hDense x hx
  simpa [hDense, interior_univ] using (Set.mem_univ x)

theorem P1_of_sUnion_eq_univ {X : Type*} [TopologicalSpace X] {ℱ : Set (Set X)} : (⋃₀ ℱ) = Set.univ → P1 (⋃₀ ℱ) := by
  intro hEq
  simpa [hEq] using (P1_univ : P1 (Set.univ : Set X))

theorem P3_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} : P3 A → P3 (e '' A) := by
  intro hP3
  intro y hy
  -- Choose a preimage point `x : X` with `y = e x`.
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` satisfies the interior/closure condition.
  have hx_int : x ∈ interior (closure (A : Set X)) := hP3 hxA
  -- The point `e x` lies in the image of this interior.
  have hmemImage : (e x : Y) ∈ (e '' interior (closure (A : Set X))) :=
    ⟨x, hx_int, rfl⟩
  ------------------------------------------------------------------
  -- 1.  The set `e '' interior (closure A)` is open.
  ------------------------------------------------------------------
  have h_open_image : IsOpen (e '' interior (closure (A : Set X))) := by
    --  It coincides with the preimage of an open set under `e.symm`.
    have h_equiv :
        (e '' interior (closure (A : Set X))) =
          (fun y : Y => e.symm y) ⁻¹' interior (closure (A : Set X)) := by
      ext y
      constructor
      · intro hy
        rcases hy with ⟨x, hx, rfl⟩
        simp [hx]
      · intro hy
        have hx : e.symm y ∈ interior (closure (A : Set X)) := hy
        exact ⟨e.symm y, hx, by simp⟩
    --  The right‐hand side is open by continuity of `e.symm`.
    have h_pre :
        IsOpen ((fun y : Y => e.symm y) ⁻¹' interior (closure (A : Set X))) := by
      exact isOpen_interior.preimage e.symm.continuous
    simpa [h_equiv] using h_pre
  ------------------------------------------------------------------
  -- 2.  This open image is contained in the interior of `e '' closure A`.
  ------------------------------------------------------------------
  have h_subset :
      (e '' interior (closure (A : Set X))) ⊆ interior (e '' closure (A : Set X)) := by
    apply interior_maximal
    · -- Inclusion into `e '' closure A`.
      intro z hz
      rcases hz with ⟨w, hw, rfl⟩
      exact ⟨w, interior_subset hw, rfl⟩
    · exact h_open_image
  have hmemInt : (e x : Y) ∈ interior (e '' closure (A : Set X)) :=
    h_subset hmemImage
  ------------------------------------------------------------------
  -- 3.  Relate `e '' closure A` with `closure (e '' A)`.
  ------------------------------------------------------------------
  have h_closure_eq :
      (e '' closure (A : Set X)) = closure (e '' (A : Set X)) := by
    simpa using e.image_closure (A : Set X)
  --  Rewrite the goal using this equality.
  simpa [h_closure_eq] using hmemInt

theorem P3_complement_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → P3 (Aᶜ) := by
  intro hClosed
  exact P3_of_P2 (P2_of_closed_complement hClosed)

theorem P1_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} : P1 B → P1 (e ⁻¹' B) := by
  intro hP1
  intro x hx
  -- `hx` gives `e x ∈ B`
  have hxB : (e x : Y) ∈ B := hx
  -- Hence `e x ∈ closure (interior B)`
  have h_closure : (e x : Y) ∈ closure (interior (B : Set Y)) := hP1 hxB
  ------------------------------------------------------------------
  -- Goal: `x ∈ closure (interior (e ⁻¹' B))`
  -- First show: `x ∈ closure (e ⁻¹' interior B)`
  ------------------------------------------------------------------
  have hx_closure_pre : (x : X) ∈ closure (e ⁻¹' interior (B : Set Y)) := by
    -- use the neighbourhood‐characterisation of closure
    apply (mem_closure_iff).2
    intro U hU hxU
    -- consider the image `e '' U`
    have hx_image : (e x : Y) ∈ e '' U := ⟨x, hxU, rfl⟩
    -- `e '' U` is open
    have h_open_image : IsOpen (e '' U) := by
      -- rewrite `e '' U` as a preimage of `U` under `e.symm`
      have h_eq : (e '' U : Set Y) = (fun y : Y => e.symm y) ⁻¹' U := by
        ext y
        constructor
        · rintro ⟨z, hzU, rfl⟩
          simpa using hzU
        · intro hy
          exact ⟨e.symm y, hy, by simp⟩
      have h_pre : IsOpen ((fun y : Y => e.symm y) ⁻¹' U) :=
        hU.preimage e.symm.continuous
      simpa [h_eq] using h_pre
    -- the closure condition yields a point in the intersection
    have h_nonempty :
        ((interior (B : Set Y)) ∩ (e '' U)).Nonempty := by
      -- use `mem_closure_iff` for `e x`
      have h := (mem_closure_iff).1 h_closure
      -- the intersection in `h` is `(e '' U) ∩ interior B`
      simpa [Set.inter_comm] using h (e '' U) h_open_image hx_image
    rcases h_nonempty with ⟨y, hy_intB, hy_image⟩
    rcases hy_image with ⟨z, hzU, hy_eq⟩
    -- `z ∈ U` and `e z ∈ interior B`
    have hz_pre : (z : X) ∈ e ⁻¹' interior (B : Set Y) := by
      have : (e z : Y) ∈ interior (B : Set Y) := by
        simpa [hy_eq] using hy_intB
      simpa using this
    -- hence `z ∈ U ∩ e ⁻¹' interior B`
    exact ⟨z, And.intro hzU hz_pre⟩
  ------------------------------------------------------------------
  -- `e ⁻¹' interior B ⊆ interior (e ⁻¹' B)` (open‐set maximality)
  ------------------------------------------------------------------
  have h_open_pre : IsOpen (e ⁻¹' interior (B : Set Y)) :=
    (isOpen_interior).preimage e.continuous
  have h_subset_pre :
      (e ⁻¹' interior (B : Set Y) : Set X) ⊆ e ⁻¹' B := by
    intro y hy
    exact (interior_subset : interior (B : Set Y) ⊆ B) hy
  have h_to_int :
      (e ⁻¹' interior (B : Set Y) : Set X) ⊆ interior (e ⁻¹' B) :=
    interior_maximal h_subset_pre h_open_pre
  have h_closure_mono :
      closure (e ⁻¹' interior (B : Set Y)) ⊆ closure (interior (e ⁻¹' B)) :=
    closure_mono h_to_int
  ------------------------------------------------------------------
  -- conclude
  ------------------------------------------------------------------
  exact h_closure_mono hx_closure_pre

theorem P2_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} : P2 A → P2 (e '' A) := by
  intro hP2
  intro y hy
  -- Pick a preimage point `x : X` with `y = e x`
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` satisfies the P2–condition
  have hx : x ∈ interior (closure (interior (A : Set X))) := hP2 hxA
  ----------------------------------------------------------------
  -- An auxiliary open set
  ----------------------------------------------------------------
  set S : Set X := interior (closure (interior (A : Set X))) with hSdef
  have hS_open : IsOpen S := by
    simpa [hSdef] using
      (isOpen_interior :
        IsOpen (interior (closure (interior (A : Set X)))))
  have hxS : x ∈ S := by
    simpa [hSdef] using hx
  ----------------------------------------------------------------
  -- The image `e '' S` is open
  ----------------------------------------------------------------
  have hImgOpen : IsOpen (e '' S) := by
    -- Express it as a preimage under the continuous map `e.symm`
    have hEq : (e '' S : Set Y) = (fun y : Y => e.symm y) ⁻¹' S := by
      ext y
      constructor
      · intro hy
        rcases hy with ⟨w, hwS, rfl⟩
        simp [hwS]
      · intro hy
        exact ⟨e.symm y, hy, by simp⟩
    simpa [hEq] using hS_open.preimage e.symm.continuous
  ----------------------------------------------------------------
  -- Inclusion:  `e '' S ⊆ closure (interior (e '' A))`
  ----------------------------------------------------------------
  have hImgSub :
      (e '' S : Set Y) ⊆ closure (interior (e '' (A : Set X))) := by
    intro z hz
    rcases hz with ⟨w, hwS, rfl⟩
    ----------------------------------------------------------------
    -- 1.  `w ∈ closure (interior A)`
    ----------------------------------------------------------------
    have hw_cl : w ∈ closure (interior (A : Set X)) := by
      -- Since `S ⊆ closure (interior A)`
      have hSsubset :
          (S : Set X) ⊆ closure (interior (A : Set X)) := by
        intro u hu
        -- `u ∈ interior (closure (interior A))`
        have huInt : u ∈
            interior (closure (interior (A : Set X))) := by
          simpa [hSdef] using hu
        -- hence in the closure
        exact (interior_subset : _ ) huInt
      exact hSsubset hwS
    ----------------------------------------------------------------
    -- 2.  `e w ∈ closure (e '' interior A)`
    ----------------------------------------------------------------
    have h_mem1 : (e w : Y) ∈ closure (e '' interior (A : Set X)) := by
      -- First land in `e '' closure (interior A)`
      have : (e w : Y) ∈ e '' closure (interior (A : Set X)) :=
        ⟨w, hw_cl, rfl⟩
      -- Then rewrite with `image_closure`
      have hEq :
          (e '' closure (interior (A : Set X))) =
            closure (e '' interior (A : Set X)) := by
        simpa using e.image_closure (interior (A : Set X))
      simpa [hEq] using this
    ----------------------------------------------------------------
    -- 3.  `closure (e '' interior A) ⊆ closure (interior (e '' A))`
    ----------------------------------------------------------------
    have hSubsetEA :
        (e '' interior (A : Set X) : Set Y) ⊆
          interior (e '' (A : Set X)) := by
      -- `e '' interior A` is open
      have hOpen_eInt : IsOpen (e '' interior (A : Set X)) := by
        -- Again use expression as a preimage
        have hEq2 :
            (e '' interior (A : Set X) : Set Y) =
              (fun y : Y => e.symm y) ⁻¹' interior (A : Set X) := by
          ext y
          constructor
          · intro hy
            rcases hy with ⟨u, huInt, rfl⟩
            simp [huInt]
          · intro hy
            exact ⟨e.symm y, hy, by simp⟩
        simpa [hEq2] using isOpen_interior.preimage e.symm.continuous
      -- and is contained in `e '' A`
      have hSub : (e '' interior (A : Set X) : Set Y) ⊆ e '' (A : Set X) := by
        intro v hv
        rcases hv with ⟨q, hqInt, rfl⟩
        exact ⟨q, interior_subset hqInt, rfl⟩
      -- apply `interior_maximal`
      exact interior_maximal hSub hOpen_eInt
    have h_closure_subset :
        closure (e '' interior (A : Set X)) ⊆
          closure (interior (e '' (A : Set X))) :=
      closure_mono hSubsetEA
    exact h_closure_subset h_mem1
  ----------------------------------------------------------------
  -- 4.  Maximality of the interior
  ----------------------------------------------------------------
  have hIncl :
      (e '' S : Set Y) ⊆
        interior (closure (interior (e '' (A : Set X)))) :=
    interior_maximal hImgSub hImgOpen
  ----------------------------------------------------------------
  -- 5.  Conclude for the original point
  ----------------------------------------------------------------
  exact hIncl ⟨x, hxS, rfl⟩

theorem P1_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P1 A) (hB : P1 B) : P1 (Set.prod A B) := by
  -- Unpack a point of `A ×ˢ B`
  rintro ⟨x, y⟩ hxy
  rcases hxy with ⟨hxA, hyB⟩
  -- Use the `P1` hypotheses for the two coordinates
  have hx_cl : x ∈ closure (interior (A : Set X)) := hA hxA
  have hy_cl : y ∈ closure (interior (B : Set Y)) := hB hyB
  -- We prove that `(x, y)` lies in the closure of the interior of `A ×ˢ B`
  apply (mem_closure_iff).2
  intro W hWopen hWmem
  -- A neighbourhood of `(x, y)` in the product gives rectangle neighbourhoods
  have hW_nhds : (W : Set (X × Y)) ∈ 𝓝 (x, y) :=
    IsOpen.mem_nhds hWopen hWmem
  rcases (mem_nhds_prod_iff).1 hW_nhds with
    ⟨U, hU_nhds, V, hV_nhds, hUVsub⟩
  -- Shrink to open sets `U₀ ⊆ U`, `V₀ ⊆ V`
  rcases (mem_nhds_iff).1 hU_nhds with
    ⟨U₀, hU₀_sub, hU₀_open, hxU₀⟩
  rcases (mem_nhds_iff).1 hV_nhds with
    ⟨V₀, hV₀_sub, hV₀_open, hyV₀⟩
  -- Use the closure conditions to pick points in the interiors
  have h_nonempty_x :
      (U₀ ∩ interior (A : Set X)).Nonempty :=
    (mem_closure_iff).1 hx_cl U₀ hU₀_open hxU₀
  rcases h_nonempty_x with ⟨x', hx'inter⟩
  have hxU₀' : (x' : X) ∈ U₀ := hx'inter.1
  have hx'Int : x' ∈ interior (A : Set X) := hx'inter.2
  have h_nonempty_y :
      (V₀ ∩ interior (B : Set Y)).Nonempty :=
    (mem_closure_iff).1 hy_cl V₀ hV₀_open hyV₀
  rcases h_nonempty_y with ⟨y', hy'inter⟩
  have hyV₀' : (y' : Y) ∈ V₀ := hy'inter.1
  have hy'Int : y' ∈ interior (B : Set Y) := hy'inter.2
  -- Show that `(x', y')` lies in `W`
  have h_in_W : (x', y') ∈ W := by
    have hxU : (x' : X) ∈ U := hU₀_sub hxU₀'
    have hyV : (y' : Y) ∈ V := hV₀_sub hyV₀'
    have h_in_UV : (x', y') ∈ U ×ˢ V := by
      exact ⟨hxU, hyV⟩
    exact hUVsub h_in_UV
  ------------------------------------------------------------------
  -- `interior A ×ˢ interior B` is contained in `interior (A ×ˢ B)`
  ------------------------------------------------------------------
  have h_subset_int :
      ((interior (A : Set X)) ×ˢ (interior (B : Set Y))) ⊆
        interior ((A : Set X) ×ˢ (B : Set Y)) := by
    -- The product of open sets is open
    have h_open :
        IsOpen (((interior (A : Set X))) ×ˢ (interior (B : Set Y))) :=
      (isOpen_interior).prod isOpen_interior
    -- It is contained in `A ×ˢ B`
    have h_sub :
        ((interior (A : Set X)) ×ˢ (interior (B : Set Y))) ⊆
          (A : Set X) ×ˢ (B : Set Y) := by
      intro p hp
      rcases hp with ⟨h1, h2⟩
      exact ⟨interior_subset h1, interior_subset h2⟩
    exact interior_maximal h_sub h_open
  -- Hence `(x', y')` lies in the interior of `A ×ˢ B`
  have h_in_int :
      (x', y') ∈ interior ((A : Set X) ×ˢ (B : Set Y)) :=
    h_subset_int ⟨hx'Int, hy'Int⟩
  -- Produce the required point in the intersection `W ∩ interior (A ×ˢ B)`
  exact ⟨(x', y'), And.intro h_in_W h_in_int⟩

theorem P2_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P2 A) (hB : P2 B) : P2 (Set.prod A B) := by
  -- Unfold `P2` for the product: we must prove
  -- `A ×ˢ B ⊆ interior (closure (interior (A ×ˢ B)))`.
  rintro ⟨x, y⟩ hxy
  rcases hxy with ⟨hxA, hyB⟩
  -- Use the `P2` hypotheses to obtain the required open neighbourhoods
  have hxU : x ∈ interior (closure (interior (A : Set X))) := hA hxA
  have hyV : y ∈ interior (closure (interior (B : Set Y))) := hB hyB
  -- Set some abbreviations
  set U : Set X := interior (closure (interior (A : Set X))) with hUdef
  set V : Set Y := interior (closure (interior (B : Set Y))) with hVdef
  have hU_open : IsOpen U := by
    simpa [hUdef] using
      (isOpen_interior : IsOpen (interior (closure (interior (A : Set X)))))
  have hV_open : IsOpen V := by
    simpa [hVdef] using
      (isOpen_interior : IsOpen (interior (closure (interior (B : Set Y)))))
  have hxU' : x ∈ U := by
    simpa [hUdef] using hxU
  have hyV' : y ∈ V := by
    simpa [hVdef] using hyV
  ------------------------------------------------------------------
  -- 1.  Show that `U ×ˢ V ⊆ closure (interior (A ×ˢ B))`.
  ------------------------------------------------------------------
  have h_prod_subset :
      (U ×ˢ V : Set (X × Y)) ⊆
        closure (interior ((A : Set X) ×ˢ (B : Set Y))) := by
    intro p hpUV
    rcases p with ⟨u, v⟩
    rcases hpUV with ⟨huU, hvV⟩
    -- From `U`/`V` to the closures of the interiors
    have hu_cl : u ∈ closure (interior (A : Set X)) :=
      interior_subset huU
    have hv_cl : v ∈ closure (interior (B : Set Y)) :=
      interior_subset hvV
    -- Prove `(u,v)` lies in the desired closure
    have : (u, v) ∈
        closure (interior ((A : Set X) ×ˢ (B : Set Y))) := by
      -- neighbourhood characterisation of closure
      apply (mem_closure_iff).2
      intro W hWopen hWmem
      -- obtain rectangle neighbourhoods
      have h_nhds : (W : Set (X × Y)) ∈ 𝓝 (u, v) :=
        IsOpen.mem_nhds hWopen hWmem
      rcases (mem_nhds_prod_iff).1 h_nhds with
        ⟨U₁, hU₁_nhds, V₁, hV₁_nhds, hUVsub⟩
      rcases (mem_nhds_iff).1 hU₁_nhds with
        ⟨U₀, hU₀_sub, hU₀_open, huU₀⟩
      rcases (mem_nhds_iff).1 hV₁_nhds with
        ⟨V₀, hV₀_sub, hV₀_open, hvV₀⟩
      -- non-empty intersections with the interior sets
      have h_nonempty_u :
          (U₀ ∩ interior (A : Set X)).Nonempty :=
        (mem_closure_iff).1 hu_cl U₀ hU₀_open huU₀
      rcases h_nonempty_u with ⟨x', hxU₀, hxIntA⟩
      have h_nonempty_v :
          (V₀ ∩ interior (B : Set Y)).Nonempty :=
        (mem_closure_iff).1 hv_cl V₀ hV₀_open hvV₀
      rcases h_nonempty_v with ⟨y', hyV₀, hyIntB⟩
      -- `(x',y') ∈ W`
      have h_in_W : (x', y') ∈ W := by
        have hxU₁ : (x' : X) ∈ U₁ := hU₀_sub hxU₀
        have hyV₁ : (y' : Y) ∈ V₁ := hV₀_sub hyV₀
        have : (x', y') ∈ U₁ ×ˢ V₁ := ⟨hxU₁, hyV₁⟩
        exact hUVsub this
      -- product of interior sets is in the interior of the product
      have h_subset_int :
          ((interior (A : Set X)) ×ˢ interior (B : Set Y)) ⊆
            interior ((A : Set X) ×ˢ (B : Set Y)) := by
        -- openness
        have h_open_prod :
            IsOpen ((interior (A : Set X)) ×ˢ interior (B : Set Y)) :=
          (isOpen_interior).prod isOpen_interior
        -- subset
        have h_sub :
            ((interior (A : Set X)) ×ˢ interior (B : Set Y)) ⊆
              (A : Set X) ×ˢ (B : Set Y) := by
          intro q hq
          rcases hq with ⟨h1, h2⟩
          exact ⟨interior_subset h1, interior_subset h2⟩
        exact interior_maximal h_sub h_open_prod
      have h_in_int :
          (x', y') ∈ interior ((A : Set X) ×ˢ (B : Set Y)) :=
        h_subset_int ⟨hxIntA, hyIntB⟩
      exact ⟨(x', y'), h_in_W, h_in_int⟩
    simpa using this
  ------------------------------------------------------------------
  -- 2.  Use interior maximality with the open set `U ×ˢ V`.
  ------------------------------------------------------------------
  have h_open_prod : IsOpen (U ×ˢ V) := hU_open.prod hV_open
  have :
      (x, y) ∈ interior (closure (interior ((A : Set X) ×ˢ (B : Set Y)))) :=
    (interior_maximal h_prod_subset h_open_prod) ⟨hxU', hyV'⟩
  simpa using this

theorem P3_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P3 A) (hB : P3 B) : P3 (Set.prod A B) := by
  -- Unpack a point in the product
  rintro ⟨x, y⟩ hxy
  rcases hxy with ⟨hxA, hyB⟩
  -- Use the `P3` hypotheses
  have hxU : x ∈ interior (closure (A : Set X)) := hA hxA
  have hyV : y ∈ interior (closure (B : Set Y)) := hB hyB
  -- Auxiliary open sets
  set U : Set X := interior (closure (A : Set X)) with hUdef
  set V : Set Y := interior (closure (B : Set Y)) with hVdef
  have hU_open : IsOpen U := by
    simpa [hUdef] using
      (isOpen_interior : IsOpen (interior (closure (A : Set X))))
  have hV_open : IsOpen V := by
    simpa [hVdef] using
      (isOpen_interior : IsOpen (interior (closure (B : Set Y))))
  have hxU' : x ∈ U := by
    simpa [hUdef] using hxU
  have hyV' : y ∈ V := by
    simpa [hVdef] using hyV
  ------------------------------------------------------------------
  -- 1.  `U ×ˢ V ⊆ closure (A ×ˢ B)`.
  ------------------------------------------------------------------
  have h_prod_subset :
      (U ×ˢ V : Set (X × Y)) ⊆
        closure ((A : Set X) ×ˢ (B : Set Y)) := by
    intro p hpUV
    rcases p with ⟨u, v⟩
    rcases hpUV with ⟨huU, hvV⟩
    -- `u ∈ closure A`, `v ∈ closure B`
    have hu_cl : u ∈ closure (A : Set X) := by
      have : u ∈ interior (closure (A : Set X)) := by
        simpa [hUdef] using huU
      exact interior_subset this
    have hv_cl : v ∈ closure (B : Set Y) := by
      have : v ∈ interior (closure (B : Set Y)) := by
        simpa [hVdef] using hvV
      exact interior_subset this
    -- Show `(u, v)` lies in the closure of `A ×ˢ B`
    have : (u, v) ∈ closure ((A : Set X) ×ˢ (B : Set Y)) := by
      apply (mem_closure_iff).2
      intro W hWopen hWmem
      -- Obtain rectangle neighbourhoods contained in `W`
      have h_nhds : (W : Set (X × Y)) ∈ 𝓝 (u, v) :=
        IsOpen.mem_nhds hWopen hWmem
      rcases (mem_nhds_prod_iff).1 h_nhds with
        ⟨U₁, hU₁_nhds, V₁, hV₁_nhds, hUVsub⟩
      rcases (mem_nhds_iff).1 hU₁_nhds with
        ⟨U₀, hU₀_sub, hU₀_open, huU₀⟩
      rcases (mem_nhds_iff).1 hV₁_nhds with
        ⟨V₀, hV₀_sub, hV₀_open, hvV₀⟩
      -- Points of `A` and `B` in these neighbourhoods
      have h_nonempty_u :
          (U₀ ∩ (A : Set X)).Nonempty :=
        (mem_closure_iff).1 hu_cl U₀ hU₀_open huU₀
      rcases h_nonempty_u with ⟨x', hxU₀, hxA'⟩
      have h_nonempty_v :
          (V₀ ∩ (B : Set Y)).Nonempty :=
        (mem_closure_iff).1 hv_cl V₀ hV₀_open hvV₀
      rcases h_nonempty_v with ⟨y', hyV₀, hyB'⟩
      -- `(x', y')` lies in `W ∩ (A ×ˢ B)`
      have h_in_W : (x', y') ∈ W := by
        have hxU₁ : (x' : X) ∈ U₁ := hU₀_sub hxU₀
        have hyV₁ : (y' : Y) ∈ V₁ := hV₀_sub hyV₀
        exact hUVsub ⟨hxU₁, hyV₁⟩
      exact ⟨(x', y'), And.intro h_in_W ⟨hxA', hyB'⟩⟩
    simpa using this
  ------------------------------------------------------------------
  -- 2.  Interior maximality with the open set `U ×ˢ V`.
  ------------------------------------------------------------------
  have h_open_prod : IsOpen (U ×ˢ V) := hU_open.prod hV_open
  have hxy_in :
      (x, y) ∈ interior (closure ((A : Set X) ×ˢ (B : Set Y))) :=
    (interior_maximal h_prod_subset h_open_prod) ⟨hxU', hyV'⟩
  simpa using hxy_in

theorem P2_iff_P1_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = Set.univ) : P2 A ↔ P1 A := by
  constructor
  · intro hP2
    intro x hx
    have hx_in : x ∈ interior (closure (interior A)) := hP2 hx
    exact (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) hx_in
  · intro _hP1
    intro x hx
    simpa [h, interior_univ] using (Set.mem_univ x)

theorem P1_univ_iff {X : Type*} [TopologicalSpace X] : P1 (Set.univ : Set X) ↔ True := by
  constructor
  · intro _
    trivial
  · intro _
    exact P1_univ

theorem P3_univ_iff {X : Type*} [TopologicalSpace X] : P3 (Set.univ : Set X) ↔ True := by
  constructor
  · intro _
    trivial
  · intro _
    exact P3_univ

theorem P1_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} : P1 A → P1 (e '' A) := by
  intro hP1
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` satisfies the `P1` condition
  have hx : x ∈ closure (interior (A : Set X)) := hP1 hxA
  ------------------------------------------------------------------
  -- 1.  `e x` lies in the closure of `e '' interior A`.
  ------------------------------------------------------------------
  have h1 : (e x : Y) ∈ closure (e '' interior (A : Set X)) := by
    have hmem : (e x : Y) ∈ e '' closure (interior (A : Set X)) :=
      ⟨x, hx, rfl⟩
    have h_eq :
        (e '' closure (interior (A : Set X))) =
          closure (e '' interior (A : Set X)) := by
      simpa using e.image_closure (interior (A : Set X))
    simpa [h_eq] using hmem
  ------------------------------------------------------------------
  -- 2.  `e '' interior A` is open and contained in `e '' A`, hence
  --     contained in `interior (e '' A)`.
  ------------------------------------------------------------------
  have hsubset :
      (e '' interior (A : Set X) : Set Y) ⊆
        interior (e '' (A : Set X)) := by
    -- openness
    have h_open : IsOpen (e '' interior (A : Set X)) := by
      -- express as a preimage under `e.symm`
      have h_eq :
          (e '' interior (A : Set X) : Set Y) =
            (fun y : Y => e.symm y) ⁻¹' interior (A : Set X) := by
        ext y
        constructor
        · intro hy
          rcases hy with ⟨u, hu, rfl⟩
          simp [hu]
        · intro hy
          exact ⟨e.symm y, hy, by simp⟩
      simpa [h_eq] using isOpen_interior.preimage e.symm.continuous
    -- inclusion into `e '' A`
    have h_incl : (e '' interior (A : Set X) : Set Y) ⊆ e '' (A : Set X) := by
      intro z hz
      rcases hz with ⟨u, huInt, rfl⟩
      exact ⟨u, interior_subset huInt, rfl⟩
    exact interior_maximal h_incl h_open
  ------------------------------------------------------------------
  -- 3.  Pass to closures and conclude.
  ------------------------------------------------------------------
  have h_closure :
      closure (e '' interior (A : Set X)) ⊆
        closure (interior (e '' (A : Set X))) :=
    closure_mono hsubset
  exact h_closure h1

theorem P2_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} : P2 B → P2 (e ⁻¹' B) := by
  intro hP2
  -- Transport `hP2` through the inverse homeomorphism `e.symm`
  have h1 : P2 (e.symm '' B) := by
    simpa using (P2_image_homeomorph e.symm) hP2
  -- Identify `e.symm '' B` with the preimage `e ⁻¹' B`
  have hEq : (e.symm '' B : Set X) = e ⁻¹' B := by
    ext x
    constructor
    · rintro ⟨y, hyB, rfl⟩
      simpa using hyB
    · intro hx
      exact ⟨e x, hx, by simp⟩
  -- Rewrite using the above equality
  simpa [hEq] using h1

theorem P3_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} : P3 B → P3 (e ⁻¹' B) := by
  intro hP3
  -- Transport `P3` through the inverse homeomorphism `e.symm`
  have h1 : P3 (e.symm '' B) := by
    simpa using (P3_image_homeomorph e.symm) hP3
  -- Identify the image with the preimage
  have hEq : (e.symm '' B : Set X) = e ⁻¹' B := by
    ext x
    constructor
    · rintro ⟨y, hyB, rfl⟩
      simpa using hyB
    · intro hx
      exact ⟨e x, hx, by simp⟩
  -- Prove the required `P3` statement
  intro x hx
  have hx' : x ∈ (e.symm '' B : Set X) := by
    simpa [hEq] using hx
  have hxInt : x ∈ interior (closure (e.symm '' B : Set X)) := h1 hx'
  simpa [hEq] using hxInt

theorem P1_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : P1 A := by
  intro x hx
  -- First, show that `A = univ` since `A` is nonempty and the space is a subsingleton.
  have hAuniv : (A : Set X) = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _;
      -- Any element `y` equals `x`, hence belongs to `A`.
      have h_eq : y = x := Subsingleton.elim y x
      simpa [h_eq] using hx
  -- Re-express the goal using this equality and finish by `simp`.
  have : (x : X) ∈ (Set.univ : Set X) := by
    trivial
  simpa [hAuniv, interior_univ, closure_univ] using this

theorem P2_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : P2 A := by
  intro x hx
  -- `A` is nonempty since it contains `x`.
  have hne : (A : Set X).Nonempty := ⟨x, hx⟩
  -- In a subsingleton every nonempty subset is the whole space.
  have hAuniv : (A : Set X) = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      rcases hne with ⟨z, hz⟩
      have : y = z := Subsingleton.elim y z
      simpa [this] using hz
  -- Rewrite the goal using `A = univ`; it reduces to `x ∈ univ`.
  have : (x : X) ∈ (Set.univ : Set X) := by
    trivial
  simpa [hAuniv, interior_univ, closure_univ, interior_univ] using this

theorem P3_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : P3 A := by
  intro x hx
  -- Since `A` is nonempty (as it contains `x`) and the space is a subsingleton,
  -- every point equals `x`, so `A = univ`.
  have hAuniv : (A : Set X) = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      have h_eq : y = x := Subsingleton.elim y x
      simpa [h_eq] using hx
  -- Rewrite the goal using this equality and conclude.
  have : (x : X) ∈ (Set.univ : Set X) := by
    trivial
  simpa [hAuniv, closure_univ, interior_univ] using this

theorem P1_of_P3_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P3 A → P1 A := by
  intro hP3
  have hP2 : P2 A := (P2_iff_P3_of_closed hA).mpr hP3
  exact P1_of_P2 hP2

theorem P2_iff_P3_of_open_complement {X : Type*} [TopologicalSpace X] {A : Set X} (h : IsOpen Aᶜ) : P2 A ↔ P3 A := by
  have hClosed : IsClosed (A : Set X) := by
    simpa using h.isClosed_compl
  simpa using (P2_iff_P3_of_closed (A := A) hClosed)

theorem P1_iff_P3_of_closed_complement {X : Type*} [TopologicalSpace X] {A : Set X} (h : IsClosed Aᶜ) : P1 A ↔ P3 A := by
  have hOpen : IsOpen (A : Set X) := by
    simpa [compl_compl] using h.isOpen_compl
  simpa using (P1_iff_P3_of_open (A := A) hOpen)

theorem closure_interior_eq_closure_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → closure (interior (A : Set X)) = closure A := by
  intro hP1
  apply Set.Subset.antisymm
  · exact closure_mono (interior_subset : (interior (A : Set X)) ⊆ A)
  · exact closure_minimal hP1 (isClosed_closure)

theorem P3_iff_P2_of_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (A : Set X) = closure (interior A)) : P3 A ↔ P2 A := by
  have hint :
      interior (closure (A : Set X)) =
        interior (closure (interior (A : Set X))) := by
    simpa [h]
  constructor
  · intro hP3
    intro x hx
    have hx' : x ∈ interior (closure (A : Set X)) := hP3 hx
    simpa [hint] using hx'
  · intro hP2
    exact P3_of_P2 hP2

theorem P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P3 (closure A) → P3 A := by
  intro hP3cl
  intro x hxA
  have hx_closure : (x : X) ∈ closure (A : Set X) := subset_closure hxA
  have hx_int : (x : X) ∈ interior (closure (closure (A : Set X))) := hP3cl hx_closure
  simpa [closure_closure] using hx_int

theorem P1_iff_P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense (interior A)) : P1 A ↔ P2 A := by
  -- Obtain the closure equality from the density assumption.
  have h_eq : closure (interior (A : Set X)) = (Set.univ : Set X) := by
    simpa using h.closure_eq
  -- Use the previously proven equivalence and flip the sides.
  simpa using (P2_iff_P1_of_dense (A := A) h_eq).symm

theorem P1_iff_closure_interior_eq_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ closure (interior (A : Set X)) = closure A := by
  constructor
  · intro hP1
    exact closure_interior_eq_closure_of_P1 (A := A) hP1
  · intro hEq
    exact P1_of_closure_interior_eq_closure (A := A) hEq

theorem P2_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} : Dense (interior A) → P2 A := by
  intro hDense
  have hEq : closure (interior (A : Set X)) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  exact P2_of_dense_interior (A := A) hEq

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} : Dense A → P3 A := by
  intro hDense
  simpa using P3_of_dense_closure (A := A) hDense.closure_eq

theorem P1_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : P1 A → P1 B → P1 C → P1 (Set.prod (Set.prod A B) C) := by
  intro hA hB hC
  have hAB : P1 (Set.prod A B) := P1_prod (A := A) (B := B) hA hB
  exact P1_prod (A := Set.prod A B) (B := C) hAB hC

theorem P1_of_finset_union {X : Type*} [TopologicalSpace X] {ι : Type*} {s : Finset ι} {A : ι → Set X} : (∀ i, i ∈ s → P1 (A i)) → P1 (⋃ i ∈ s, A i) := by
  classical
  intro hAll
  -- We build the required statement by induction on the finset `s`.
  have hMain :
      (∀ i, i ∈ s → P1 (A i)) → P1 (⋃ i ∈ s, A i) := by
    refine s.induction ?hbase ?hstep
    -- Base case: `s = ∅`
    · intro _hAll
      simpa using (P1_empty : P1 (∅ : Set X))
    -- Induction step: add an element `a`
    · intro a t ha_not_mem ih hAll'
      -- `P1` for the new element `a`
      have hA : P1 (A a) :=
        hAll' a (by
          have : (a : ι) ∈ insert a t := Finset.mem_insert_self a t
          exact this)
      -- `P1` for the old finset `t`
      have hT : P1 (⋃ i ∈ t, A i) := ih (by
        intro i hi_t
        exact hAll' i (Finset.mem_insert_of_mem hi_t))
      -- Combine the two using `P1_union`
      have h_union : P1 ((A a) ∪ ⋃ i ∈ t, A i) := P1_union hA hT
      -- Identify the two unions
      have h_eq :
          (⋃ i ∈ insert a t, A i) = (A a) ∪ ⋃ i ∈ t, A i := by
        ext x
        constructor
        · intro hx
          rcases Set.mem_iUnion.1 hx with ⟨i, hx⟩
          rcases Set.mem_iUnion.1 hx with ⟨hi_insert, hxAi⟩
          have hmem : i = a ∨ i ∈ t := (Finset.mem_insert).1 hi_insert
          cases hmem with
          | inl h_eq_i =>
              cases h_eq_i
              exact Or.inl hxAi
          | inr hi_t =>
              have : x ∈ ⋃ i ∈ t, A i := by
                refine Set.mem_iUnion.2 ⟨i, ?_⟩
                refine Set.mem_iUnion.2 ⟨hi_t, hxAi⟩
              exact Or.inr this
        · intro hx
          cases hx with
          | inl hxA =>
              exact
                Set.mem_iUnion.2
                  ⟨a, Set.mem_iUnion.2 ⟨Finset.mem_insert_self a t, hxA⟩⟩
          | inr hx_t =>
              rcases Set.mem_iUnion.1 hx_t with ⟨i, hx_i⟩
              rcases Set.mem_iUnion.1 hx_i with ⟨hi_t, hxAi⟩
              exact
                Set.mem_iUnion.2
                  ⟨i, Set.mem_iUnion.2 ⟨Finset.mem_insert_of_mem hi_t, hxAi⟩⟩
      simpa [h_eq] using h_union
  exact hMain hAll

theorem P2_of_P3_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P3 A → P2 A := by
  intro hP3
  exact ((P2_iff_P3_of_closed (A := A) hA).mpr hP3)

theorem P3_of_P1_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P1 A → P3 A := by
  intro _hP1
  exact P3_of_open (A := A) hA

theorem P1_complement_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → P1 (Aᶜ) := by
  intro hClosed
  exact P1_of_P2 (A := Aᶜ) (P2_of_closed_complement (A := A) hClosed)

theorem P3_clopen_iff {X : Type*} [TopologicalSpace X] {A : Set X} (hA₁ : IsOpen A) (hA₂ : IsClosed A) : P3 A ↔ True := by
  constructor
  · intro _; trivial
  · intro _; exact P3_of_open (A := A) hA₁

theorem P2_exists_subset {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → ∃ U, IsOpen U ∧ U ⊆ A := by
  intro _
  exact ⟨interior A, isOpen_interior, interior_subset⟩

theorem P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → P1 (closure A) := by
  intro hP1
  intro x hx
  -- `hP1` gives the inclusion `A ⊆ closure (interior A)`.
  have hP1_sub : (A : Set X) ⊆ closure (interior (A : Set X)) := hP1
  -- Taking closures on both sides yields
  -- `closure A ⊆ closure (interior A)`.
  have h_closure_subset :
      closure (A : Set X) ⊆ closure (interior (A : Set X)) := by
    simpa [closure_closure] using closure_mono hP1_sub
  -- Hence `x ∈ closure (interior A)`.
  have hx₁ : (x : X) ∈ closure (interior (A : Set X)) :=
    h_closure_subset hx
  -- Monotonicity of `interior`, followed by `closure`, gives
  -- `closure (interior A) ⊆ closure (interior (closure A))`.
  have h_closure_step :
      closure (interior (A : Set X)) ⊆
        closure (interior (closure (A : Set X))) := by
    have h_int_subset :
        interior (A : Set X) ⊆ interior (closure (A : Set X)) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    exact closure_mono h_int_subset
  -- Combine the two inclusions to reach the goal.
  exact h_closure_step hx₁

theorem P2_inter {X : Type*} [TopologicalSpace X] {A B : Set X} : P2 A → P2 B → P2 (A ∩ B) := by
  --  First, unpack the two `P2` hypotheses.
  intro hA hB
  intro x hx
  rcases hx with ⟨hxA, hxB⟩
  --  Points furnished by the two inclusions.
  have hxA' : x ∈ interior (closure (interior (A : Set X))) := hA hxA
  have hxB' : x ∈ interior (closure (interior (B : Set X))) := hB hxB
  ----------------------------------------------------------------
  --  Define an auxiliary open neighbourhood of `x`.
  ----------------------------------------------------------------
  let O : Set X :=
    interior (closure (interior (A : Set X))) ∩
      interior (closure (interior (B : Set X)))
  have hOopen : IsOpen O :=
    (isOpen_interior.inter isOpen_interior)
  have hxO : (x : X) ∈ O := by
    dsimp [O] at *
    exact And.intro hxA' hxB'
  ----------------------------------------------------------------
  --  Key inclusion: `O ⊆ closure (interior (A ∩ B))`.
  ----------------------------------------------------------------
  have hOsub :
      (O : Set X) ⊆ closure (interior ((A ∩ B : Set X))) := by
    intro y hy
    rcases hy with ⟨hyA', hyB'⟩
    --  `y` is in the two closures of the interiors.
    have hyA_cl : y ∈ closure (interior (A : Set X)) :=
      interior_subset hyA'
    have hyB_cl : y ∈ closure (interior (B : Set X)) :=
      interior_subset hyB'
    --  We show directly that `y ∈ closure (interior (A ∩ B))`.
    have : y ∈ closure (interior ((A ∩ B : Set X))) := by
      --  Use the neighbourhood characterisation of the closure.
      apply (mem_closure_iff).2
      intro U hUopen hyU
      ----------------------------------------------------------------
      --  Build a smaller open set `W` lying inside the two big closures.
      ----------------------------------------------------------------
      let W : Set X :=
        U ∩ interior (closure (interior (A : Set X))) ∩
          interior (closure (interior (B : Set X)))
      have hWopen : IsOpen W := by
        have h₁ : IsOpen (U ∩ interior (closure (interior (A : Set X)))) :=
          hUopen.inter isOpen_interior
        simpa [W] using h₁.inter isOpen_interior
      have hyW : (y : X) ∈ W := by
        dsimp [W] at *
        exact ⟨⟨hyU, hyA'⟩, hyB'⟩
      ----------------------------------------------------------------
      --  `W` meets `interior A`.
      ----------------------------------------------------------------
      have hnonA : (W ∩ interior (A : Set X)).Nonempty := by
        have h := (mem_closure_iff).1 hyA_cl
        have h' := h W hWopen hyW
        --  Re‐arrange the intersection to the desired shape.
        simpa [W, Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using h'
      rcases hnonA with ⟨a, haW, haIntA⟩
      ----------------------------------------------------------------
      --  Shrink once more inside `interior A`.
      ----------------------------------------------------------------
      let V : Set X := interior (A : Set X) ∩ W
      have hVopen : IsOpen V := isOpen_interior.inter hWopen
      have haV : (a : X) ∈ V := by
        dsimp [V] at *
        exact ⟨haIntA, haW⟩
      --  `a ∈ closure (interior B)` (since `a ∈ W`).
      have ha_clB : a ∈ closure (interior (B : Set X)) := by
        have : (a : X) ∈ interior (closure (interior (B : Set X))) := by
          --  Extract the relevant component of `a ∈ W`.
          have hAW : a ∈ W := haW
          dsimp [W] at hAW
          exact hAW.2
        exact interior_subset this
      ----------------------------------------------------------------
      --  Hence `V` meets `interior B`.
      ----------------------------------------------------------------
      have hnonB : (V ∩ interior (B : Set X)).Nonempty := by
        have h := (mem_closure_iff).1 ha_clB
        have h' := h V hVopen haV
        simpa [V, Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using h'
      rcases hnonB with ⟨z, hzV, hzIntB⟩
      --  Summarise the information on `z`.
      have hzIntA : z ∈ interior (A : Set X) := hzV.1
      have hzW   : z ∈ W := hzV.2
      have hzU   : (z : X) ∈ U := by
        dsimp [W] at hzW
        exact hzW.1.1
      --  `z` lies in the interior of `A ∩ B`.
      have hzIntAB : (z : X) ∈ interior ((A ∩ B : Set X)) := by
        --  `interior (A ∩ B) = interior A ∩ interior B`
        have : z ∈ interior (A : Set X) ∩ interior (B : Set X) :=
          ⟨hzIntA, hzIntB⟩
        simpa [interior_inter] using this
      --  Produce the required intersection point.
      exact ⟨z, hzU, hzIntAB⟩
    exact this
  ----------------------------------------------------------------
  --  Apply `interior_maximal` to obtain the desired membership.
  ----------------------------------------------------------------
  have hfinal :
      x ∈ interior (closure (interior ((A ∩ B : Set X)))) :=
    (interior_maximal hOsub hOopen) hxO
  simpa using hfinal

theorem P2_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : P2 A → P2 B → P2 C → P2 (Set.prod (Set.prod A B) C) := by
  intro hA hB hC
  have hAB : P2 (Set.prod A B) := P2_prod (A := A) (B := B) hA hB
  exact P2_prod (A := Set.prod A B) (B := C) hAB hC

theorem P3_closure_univ {X : Type*} [TopologicalSpace X] {A : Set X} : closure A = Set.univ → P3 (closure A) := by
  intro h
  intro x hx
  simpa [closure_closure, h, interior_univ] using hx

theorem P3_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : P3 A → P3 B → P3 C → P3 (Set.prod (Set.prod A B) C) := by
  intro hA hB hC
  have hAB : P3 (Set.prod A B) := P3_prod (A := A) (B := B) hA hB
  exact P3_prod (A := Set.prod A B) (B := C) hAB hC

theorem P2_prod_four {W X Y Z : Type*} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set W} {B : Set X} {C : Set Y} {D : Set Z} : P2 A → P2 B → P2 C → P2 D → P2 (Set.prod (Set.prod (Set.prod A B) C) D) := by
  intro hA hB hC hD
  have hABC : P2 (Set.prod (Set.prod A B) C) :=
    P2_prod_three (A := A) (B := B) (C := C) hA hB hC
  exact P2_prod (A := Set.prod (Set.prod A B) C) (B := D) hABC hD

theorem P1_prod_four {W X Y Z : Type*} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set W} {B : Set X} {C : Set Y} {D : Set Z} : P1 A → P1 B → P1 C → P1 D → P1 (Set.prod (Set.prod (Set.prod A B) C) D) := by
  intro hA hB hC hD
  have hABC : P1 (Set.prod (Set.prod A B) C) :=
    P1_prod_three (A := A) (B := B) (C := C) hA hB hC
  exact
    P1_prod (A := Set.prod (Set.prod A B) C) (B := D) hABC hD

theorem P3_prod_four {W X Y Z : Type*} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set W} {B : Set X} {C : Set Y} {D : Set Z} : P3 A → P3 B → P3 C → P3 D → P3 (Set.prod (Set.prod (Set.prod A B) C) D) := by
  intro hA hB hC hD
  have hABC : P3 (Set.prod (Set.prod A B) C) :=
    P3_prod_three (A := A) (B := B) (C := C) hA hB hC
  exact
    P3_prod (A := Set.prod (Set.prod A B) C) (B := D) hABC hD

theorem P2_of_P1_dense {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → Dense (interior A) → P2 A := by
  intro _ hDense x hx
  have hEq : closure (interior (A : Set X)) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  simpa [hEq, interior_univ] using (Set.mem_univ x)

theorem P3_of_P1_dense {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → Dense (interior A) → P3 A := by
  intro _hP1 hDense
  intro x hx
  -- The closure of `interior A` is the whole space, by density.
  have h_univ : closure (interior (A : Set X)) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  -- Hence every point belongs to the interior of this closure.
  have hx_int :
      x ∈ interior (closure (interior (A : Set X))) := by
    have : (x : X) ∈ (Set.univ : Set X) := by
      simp
    simpa [h_univ, interior_univ] using this
  -- Monotonicity: the interior of `closure (interior A)` is contained in the
  -- interior of `closure A`.
  have h_subset :
      interior (closure (interior (A : Set X))) ⊆
        interior (closure (A : Set X)) := by
    have h_cl :
        closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
      closure_mono (interior_subset : interior (A : Set X) ⊆ A)
    exact interior_mono h_cl
  exact h_subset hx_int

theorem P2_of_sigma {X : Type*} [TopologicalSpace X] {ι : Type*} {A : ι → Set X} : (∀ i, P2 (A i)) → P2 {x : X | ∃ i, x ∈ A i} := by
  intro hAll
  -- `P2` holds for the indexed union `⋃ i, A i`.
  have hP2Union : P2 (Set.iUnion A) := (P2_iUnion (A := A)) hAll
  -- Identify the two sets.
  have hEq : ({x : X | ∃ i, x ∈ A i} : Set X) = Set.iUnion A := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨i, hxi⟩
      exact Set.mem_iUnion.2 ⟨i, hxi⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
      exact ⟨i, hxi⟩
  -- Transport the property along this equality.
  simpa [hEq] using hP2Union

theorem P2_prod_five {V W X Y Z : Type*} [TopologicalSpace V] [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set V} {B : Set W} {C : Set X} {D : Set Y} {E : Set Z} : P2 A → P2 B → P2 C → P2 D → P2 E → P2 (Set.prod (Set.prod (Set.prod (Set.prod A B) C) D) E) := by
  intro hA hB hC hD hE
  have hABCD : P2 (Set.prod (Set.prod (Set.prod A B) C) D) :=
    P2_prod_four (A := A) (B := B) (C := C) (D := D) hA hB hC hD
  exact
    P2_prod (A := Set.prod (Set.prod (Set.prod A B) C) D) (B := E) hABCD hE

theorem P1_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} : P1 A → P1 B → P1 C → P1 (A ∪ B ∪ C) := by
  intro hA hB hC
  -- First combine `A` and `B`
  have hAB : P1 (A ∪ B) := P1_union (A := A) (B := B) hA hB
  -- Then add `C`
  have hABC : P1 ((A ∪ B) ∪ C) := P1_union (A := A ∪ B) (B := C) hAB hC
  -- Rewrite the union to the required form
  simpa [Set.union_assoc] using hABC

theorem P1_iff_P2_of_dense_closure {X : Type*} [TopologicalSpace X] {A : Set X} : closure A = Set.univ → (P1 A ↔ P2 A) := by
  intro hCl
  have hP1_to_P2 : P1 A → P2 A := by
    intro hP1
    intro x _
    -- From `hP1` we get `closure (interior A) = closure A = univ`.
    have h_cl_int_univ : closure (interior (A : Set X)) = (Set.univ : Set X) := by
      have hEq := closure_interior_eq_closure_of_P1 (A := A) hP1
      simpa [hCl] using hEq
    -- Hence the interior of this closure is the whole space.
    have : (x : X) ∈ (Set.univ : Set X) := by
      simp
    simpa [h_cl_int_univ, interior_univ] using this
  exact ⟨hP1_to_P2, P1_of_P2⟩

theorem P2_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} : P2 A → P2 B → P2 C → P2 (A ∪ B ∪ C) := by
  intro hA hB hC
  -- First, combine `A` and `B`
  have hAB : P2 (A ∪ B) := P2_union (A := A) (B := B) hA hB
  -- Then add `C`
  have hABC : P2 ((A ∪ B) ∪ C) := P2_union (A := A ∪ B) (B := C) hAB hC
  -- Rewrite the union to the required form
  simpa [Set.union_assoc] using hABC

theorem P3_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} : P3 A → P3 B → P3 C → P3 (A ∪ B ∪ C) := by
  intro hA hB hC
  -- Combine `A` and `B`
  have hAB : P3 (A ∪ B) := P3_union (A := A) (B := B) hA hB
  -- Then add `C`
  have hABC : P3 ((A ∪ B) ∪ C) := P3_union (A := A ∪ B) (B := C) hAB hC
  -- Rewrite the union to the required form
  simpa [Set.union_assoc] using hABC

theorem P1_exists_open_subset {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → ∃ U, IsOpen U ∧ U ⊆ A ∧ P1 U := by
  intro _hP1
  exact
    ⟨interior A, isOpen_interior, interior_subset,
      (P1_interior (X := X) (A := A))⟩

theorem P2_exists_open_subset {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → ∃ U, IsOpen U ∧ U ⊆ A ∧ P2 U := by
  intro _hP2
  exact
    ⟨interior A, isOpen_interior, interior_subset, (P2_interior (X := X) (A := A))⟩

theorem P3_exists_open_subset {X : Type*} [TopologicalSpace X] {A : Set X} : P3 A → ∃ U, IsOpen U ∧ U ⊆ A ∧ P3 U := by
  intro hP3
  exact
    ⟨interior A, isOpen_interior, interior_subset,
      P3_interior (X := X) (A := A) hP3⟩

theorem P1_sigma {X : Type*} [TopologicalSpace X] {ι : Type*} {A : ι → Set X} : (∀ i, P1 (A i)) → P1 {x : X | ∃ i, x ∈ A i} := by
  intro hAll
  -- First, `P1` holds for the indexed union `⋃ i, A i`.
  have hP1Union : P1 (Set.iUnion A) := (P1_iUnion (A := A)) hAll
  -- Identify the two sets.
  have hEq : ({x : X | ∃ i, x ∈ A i} : Set X) = Set.iUnion A := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨i, hxi⟩
      exact Set.mem_iUnion.2 ⟨i, hxi⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
      exact ⟨i, hxi⟩
  -- Transport the property along the equality.
  simpa [hEq] using hP1Union

theorem P3_prod_five {V W X Y Z : Type*} [TopologicalSpace V] [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set V} {B : Set W} {C : Set X} {D : Set Y} {E : Set Z} : P3 A → P3 B → P3 C → P3 D → P3 E → P3 (Set.prod (Set.prod (Set.prod (Set.prod A B) C) D) E) := by
  intro hA hB hC hD hE
  have hABCD : P3 (Set.prod (Set.prod (Set.prod A B) C) D) :=
    P3_prod_four (A := A) (B := B) (C := C) (D := D) hA hB hC hD
  exact
    P3_prod (A := Set.prod (Set.prod (Set.prod A B) C) D) (B := E) hABCD hE

theorem P1_exists_closed_subset {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → ∃ F, IsClosed F ∧ F ⊆ A ∧ P1 F := by
  intro _
  exact ⟨(∅ : Set X), isClosed_empty, Set.empty_subset _, (P1_empty : P1 (∅ : Set X))⟩

theorem P3_union_left_P2 {X : Type*} [TopologicalSpace X] {A B : Set X} : P2 A → P3 B → P3 (A ∪ B) := by
  intro hP2A hP3B
  have hP3A : P3 A := P3_of_P2 hP2A
  exact P3_union (A := A) (B := B) hP3A hP3B

theorem P1_exists_compact_subset {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → ∃ K, IsCompact K ∧ K ⊆ A := by
  intro _
  exact ⟨(∅ : Set X), isCompact_empty, Set.empty_subset _⟩

theorem P2_prod_swap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P2 (Set.prod A B) → P2 (Set.prod B A) := by
  intro hP2
  -- The swap homeomorphism between `X × Y` and `Y × X`.
  let e : X × Y ≃ₜ Y × X := Homeomorph.prodComm (X := X) (Y := Y)
  -- Transport `P2` through this homeomorphism.
  have hImage : P2 (e '' (Set.prod A B)) :=
    (P2_image_homeomorph (e := e) (A := Set.prod A B)) hP2
  -- Identify the image with `B ×ˢ A`.
  have hEq : (e '' (Set.prod A B) : Set (Y × X)) = Set.prod B A := by
    ext p
    constructor
    · rintro ⟨q, hqAB, rfl⟩
      rcases q with ⟨x, y⟩
      rcases hqAB with ⟨hxA, hyB⟩
      exact And.intro hyB hxA
    · intro hp
      rcases p with ⟨y, x⟩
      rcases hp with ⟨hyB, hxA⟩
      refine ⟨(x, y), ?_, ?_⟩
      · exact And.intro hxA hyB
      · rfl
  -- Conclude using the set equality.
  simpa [hEq] using hImage

theorem P2_singleton_of_discrete {X : Type*} [TopologicalSpace X] [DiscreteTopology X] {x : X} : P2 ({x} : Set X) := by
  intro y hy
  -- In a discrete space every set is both open and closed, so taking `interior`
  -- or `closure` does not change it.
  have h₁ : interior ({x} : Set X) = ({x} : Set X) :=
    (isOpen_discrete ({x} : Set X)).interior_eq
  have h₂ : closure ({x} : Set X) = ({x} : Set X) :=
    (isClosed_discrete ({x} : Set X)).closure_eq
  simpa [h₁, h₂] using hy

theorem P3_singleton_of_discrete {X : Type*} [TopologicalSpace X] [DiscreteTopology X] {x : X} : P3 ({x} : Set X) := by
  intro y hy
  simpa [ (isClosed_discrete ({x} : Set X)).closure_eq,
          (isOpen_discrete ({x} : Set X)).interior_eq ] using hy

theorem P3_of_sigma {X : Type*} [TopologicalSpace X] {ι : Type*} {A : ι → Set X} : (∀ i, P3 (A i)) → P3 {x : X | ∃ i, x ∈ A i} := by
  intro hAll
  -- `P3` holds for the indexed union `⋃ i, A i`.
  have hP3Union : P3 (Set.iUnion A) := (P3_iUnion (A := A)) hAll
  -- Identify the sigma‐type set with the union.
  have hEq : ({x : X | ∃ i, x ∈ A i} : Set X) = Set.iUnion A := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨i, hxi⟩
      exact Set.mem_iUnion.2 ⟨i, hxi⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
      exact ⟨i, hxi⟩
  -- Transport the property along this equality.
  simpa [hEq] using hP3Union

theorem P2_closure_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → closure (interior A) = closure A := by
  intro hP2
  exact closure_interior_eq_closure_of_P1 (A := A) (P1_of_P2 (A := A) hP2)

theorem P3_prod_univ_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : P3 A → P3 (Set.prod A (Set.univ : Set Y)) := by
  intro hA
  have hUniv : P3 (Set.univ : Set Y) := P3_univ
  simpa using (P3_prod (A := A) (B := (Set.univ : Set Y)) hA hUniv)

theorem P2_prod_univ_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} : P2 B → P2 (Set.prod (Set.univ : Set X) B) := by
  intro hB
  simpa using (P2_prod (A := (Set.univ : Set X)) (B := B) P2_univ hB)

theorem P1_univ_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] : P1 (Set.prod (Set.univ : Set X) (Set.univ : Set Y)) := by
  simpa using
    (P1_prod
      (A := (Set.univ : Set X))
      (B := (Set.univ : Set Y))
      (P1_univ (X := X))
      (P1_univ (X := Y)))

theorem P1_subset_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → ∃ U, IsOpen U ∧ U ⊆ A ∧ P1 U := by
  intro hP2
  rcases (P2_exists_open_subset (A := A) hP2) with ⟨U, hUopen, hUsub, hP2U⟩
  exact ⟨U, hUopen, hUsub, P1_of_P2 hP2U⟩

theorem P1_union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X} : P1 A → P1 B → P1 C → P1 D → P1 (A ∪ B ∪ C ∪ D) := by
  intro hA hB hC hD
  -- Combine the first three sets
  have hABC : P1 (A ∪ B ∪ C) :=
    P1_union_three (A := A) (B := B) (C := C) hA hB hC
  -- Now add the fourth set
  have hABCD : P1 ((A ∪ B ∪ C) ∪ D) :=
    P1_union (A := A ∪ B ∪ C) (B := D) hABC hD
  simpa [Set.union_assoc] using hABCD

theorem P2_union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X} : P2 A → P2 B → P2 C → P2 D → P2 (A ∪ B ∪ C ∪ D) := by
  intro hA hB hC hD
  -- First, combine `A`, `B`, and `C`.
  have hABC : P2 (A ∪ B ∪ C) :=
    P2_union_three (A := A) (B := B) (C := C) hA hB hC
  -- Then add `D`.
  have hABCD : P2 ((A ∪ B ∪ C) ∪ D) :=
    P2_union (A := A ∪ B ∪ C) (B := D) hABC hD
  simpa [Set.union_assoc] using hABCD

theorem P3_union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X} : P3 A → P3 B → P3 C → P3 D → P3 (A ∪ B ∪ C ∪ D) := by
  intro hA hB hC hD
  -- Combine the first three sets
  have hABC : P3 (A ∪ B ∪ C) :=
    P3_union_three (A := A) (B := B) (C := C) hA hB hC
  -- Now add the fourth set
  have hABCD : P3 ((A ∪ B ∪ C) ∪ D) :=
    P3_union (A := A ∪ B ∪ C) (B := D) hABC hD
  -- Rewrite to the desired union of four sets
  simpa [Set.union_assoc] using hABCD

theorem P1_prod_comm_eq {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P1 (Set.prod A B) ↔ P1 (Set.prod B A) := by
  -- The swap homeomorphism between `X × Y` and `Y × X`.
  let e : X × Y ≃ₜ Y × X := Homeomorph.prodComm (X := X) (Y := Y)
  -- Forward implication:  `P1 (A × B) → P1 (B × A)`.
  have hforward : P1 (Set.prod A B) → P1 (Set.prod B A) := by
    intro hAB
    -- Transport through the homeomorphism.
    have hImage : P1 (e '' (Set.prod A B)) :=
      (P1_image_homeomorph (e := e) (A := Set.prod A B)) hAB
    -- Identify the image with `B ×ˢ A`.
    have hEq : (e '' (Set.prod A B) : Set (Y × X)) = Set.prod B A := by
      ext p
      constructor
      · rintro ⟨q, hq, rfl⟩
        rcases q with ⟨x, y⟩
        rcases hq with ⟨hx, hy⟩
        exact And.intro hy hx
      · intro hp
        rcases p with ⟨y, x⟩
        rcases hp with ⟨hy, hx⟩
        refine ⟨(x, y), ?_, ?_⟩
        · exact And.intro hx hy
        · rfl
    simpa [hEq] using hImage
  -- Backward implication:  `P1 (B × A) → P1 (A × B)`.
  have hbackward : P1 (Set.prod B A) → P1 (Set.prod A B) := by
    intro hBA
    -- Use the inverse homeomorphism.
    have hImage : P1 (e.symm '' (Set.prod B A)) :=
      (P1_image_homeomorph (e := e.symm) (A := Set.prod B A)) hBA
    -- Identify the image with `A ×ˢ B`.
    have hEq : (e.symm '' (Set.prod B A) : Set (X × Y)) = Set.prod A B := by
      ext p
      constructor
      · rintro ⟨q, hq, rfl⟩
        rcases q with ⟨y, x⟩
        rcases hq with ⟨hy, hx⟩
        exact And.intro hx hy
      · intro hp
        rcases p with ⟨x, y⟩
        rcases hp with ⟨hx, hy⟩
        refine ⟨(y, x), ?_, ?_⟩
        · exact And.intro hy hx
        · rfl
    simpa [hEq] using hImage
  -- Assemble the equivalence.
  exact ⟨hforward, hbackward⟩