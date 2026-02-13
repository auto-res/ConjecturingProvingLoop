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


theorem P1_empty {X : Type*} [TopologicalSpace X] : P1 (∅ : Set X) := by
  intro x hx
  have hfalse : False := by
    simpa [Set.mem_empty_iff_false] using hx
  exact hfalse.elim

theorem P2_univ {X : Type*} [TopologicalSpace X] : P2 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P3 (interior A) := by
  intro x hx
  have hsubset : (interior A) ⊆ interior (closure (interior A)) := by
    apply interior_maximal
    · exact subset_closure
    · exact isOpen_interior
  exact hsubset hx

theorem P2_subset_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P1 A := by
  intro hP2 x hx
  exact interior_subset (hP2 hx)

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {ℬ : Set (Set X)} : (∀ A ∈ ℬ, P1 A) → P1 (⋃₀ ℬ) := by
  intro h
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hAℬ, hxA⟩
  have hx_closure : x ∈ closure (interior A) := (h A hAℬ) hxA
  have hsubset : closure (interior A) ⊆ closure (interior (⋃₀ ℬ)) := by
    apply closure_mono
    apply interior_mono
    exact Set.subset_sUnion_of_mem hAℬ
  exact hsubset hx_closure

theorem P2_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {s : ι → Set X} : (∀ i, P2 (s i)) → P2 (⋃ i, s i) := by
  intro hP2
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have hx_in : x ∈ interior (closure (interior (s i))) := (hP2 i) hx_i
  have h_subset :
      interior (closure (interior (s i))) ⊆
        interior (closure (interior (⋃ j, s j))) := by
    apply interior_mono
    apply closure_mono
    apply interior_mono
    exact Set.subset_iUnion _ i
  exact h_subset hx_in

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {ℬ : Set (Set X)} : (∀ A ∈ ℬ, P3 A) → P3 (⋃₀ ℬ) := by
  intro hP3 x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hAℬ, hxA⟩
  have hx_in : x ∈ interior (closure A) := (hP3 A hAℬ) hxA
  have h_subset : interior (closure A) ⊆ interior (closure (⋃₀ ℬ)) := by
    apply interior_mono
    apply closure_mono
    exact Set.subset_sUnion_of_mem hAℬ
  exact h_subset hx_in

theorem P3_univ {X : Type*} [TopologicalSpace X] : P3 (Set.univ : Set X) := by
  intro x hx
  simpa [closure_univ, interior_univ] using hx

theorem P2_empty {X : Type*} [TopologicalSpace X] : P2 (∅ : Set X) := by
  intro x hx
  have hfalse : False := by
    simpa [Set.mem_empty_iff_false] using hx
  exact hfalse.elim

theorem P2_self {X : Type*} [TopologicalSpace X] {A : Set X} : P2 (interior A) := by
  intro x hx
  have hsubset : interior A ⊆ interior (closure (interior A)) := by
    apply interior_maximal
    · exact subset_closure
    · exact isOpen_interior
  simpa [interior_interior] using (hsubset hx)

theorem P3_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {s : ι → Set X} : (∀ i, P3 (s i)) → P3 (⋃ i, s i) := by
  intro hP3 x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have hx_in : x ∈ interior (closure (s i)) := (hP3 i) hx_i
  have h_subset :
      interior (closure (s i)) ⊆
        interior (closure (⋃ j, s j)) := by
    apply interior_mono
    apply closure_mono
    exact Set.subset_iUnion _ i
  exact h_subset hx_in

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P1 A) (hB : P1 B) : P1 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA_mem =>
      -- `x` comes from `A`
      have hx_closure : x ∈ closure (interior A) := hA hA_mem
      have h_subset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        exact Set.subset_union_left
      exact h_subset hx_closure
  | inr hB_mem =>
      -- `x` comes from `B`
      have hx_closure : x ∈ closure (interior B) := hB hB_mem
      have h_subset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        exact Set.subset_union_right
      exact h_subset hx_closure

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P2 A) (hB : P2 B) : P2 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA_mem =>
      have hx_in : x ∈ interior (closure (interior A)) := hA hA_mem
      have h_subset :
          interior (closure (interior A)) ⊆
            interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        apply closure_mono
        apply interior_mono
        exact Set.subset_union_left
      exact h_subset hx_in
  | inr hB_mem =>
      have hx_in : x ∈ interior (closure (interior B)) := hB hB_mem
      have h_subset :
          interior (closure (interior B)) ⊆
            interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        apply closure_mono
        apply interior_mono
        exact Set.subset_union_right
      exact h_subset hx_in

theorem P2_subset_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P3 A := by
  intro hP2
  intro x hxA
  have hx_in : x ∈ interior (closure (interior A)) := hP2 hxA
  have h_subset : interior (closure (interior A)) ⊆ interior (closure A) := by
    apply interior_mono
    apply closure_mono
    exact interior_subset
  exact h_subset hx_in

theorem P3_open {X : Type*} [TopologicalSpace X] {A : Set X} (h_open : IsOpen A) : P3 A := by
  intro x hxA
  -- Since `A` is open, its interior is itself.
  have h_eq : interior A = A := h_open.interior_eq
  -- `interior A` is contained in `interior (closure A)` because `A ⊆ closure A`.
  have h_subset : interior A ⊆ interior (closure A) := by
    apply interior_mono
    exact subset_closure
  -- The desired conclusion follows from the two facts above.
  have hx_interiorA : x ∈ interior A := by
    simpa [h_eq] using hxA
  exact h_subset hx_interiorA

theorem P2_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A := by
  intro x hxA
  -- Since `A` is open, its interior is itself.
  have h_eq : interior A = A := hA.interior_eq
  -- Hence `x` belongs to `interior A`.
  have hx_intA : x ∈ interior A := by
    simpa [h_eq] using hxA
  -- `interior A` is open and contained in `closure (interior A)`,
  -- so it is contained in `interior (closure (interior A))`.
  have h_subset : interior A ⊆ interior (closure (interior A)) := by
    apply interior_maximal
    · exact subset_closure
    · exact isOpen_interior
  -- Finish the proof.
  exact h_subset hx_intA

theorem P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h_dense : closure (interior A) = Set.univ) : P1 A := by
  intro x hx
  simpa [h_dense] using (Set.mem_univ x)

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h_dense : closure (interior A) = Set.univ) : P2 A := by
  intro x hx
  simpa [h_dense, interior_univ] using (Set.mem_univ x)

theorem P1_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} (hA : P1 A) (hB : P1 B) (hC : P1 C) : P1 (A ∪ B ∪ C) := by
  have hAB : P1 (A ∪ B) := P1_union hA hB
  simpa using P1_union hAB hC

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {ℬ : Set (Set X)} : (∀ A ∈ ℬ, P2 A) → P2 (⋃₀ ℬ) := by
  intro hP2
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hAℬ, hxA⟩
  have hx_in : x ∈ interior (closure (interior A)) := (hP2 A hAℬ) hxA
  have h_subset :
      interior (closure (interior A)) ⊆
        interior (closure (interior (⋃₀ ℬ))) := by
    apply interior_mono
    apply closure_mono
    apply interior_mono
    exact Set.subset_sUnion_of_mem hAℬ
  exact h_subset hx_in

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} : closure A = Set.univ → P3 A := by
  intro h_dense x hx
  simpa [h_dense, interior_univ] using (Set.mem_univ x)

theorem P1_iff_eq {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ closure (interior A) = closure A := by
  constructor
  · intro hP1
    have h₁ : closure (interior A) ⊆ closure A := by
      exact closure_mono interior_subset
    have h₂ : closure A ⊆ closure (interior A) := by
      have := closure_mono hP1
      simpa [closure_closure] using this
    exact subset_antisymm h₁ h₂
  · intro h_eq
    intro x hxA
    have hx_closure : x ∈ closure A := subset_closure hxA
    simpa [h_eq] using hx_closure

theorem P1_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {s : ι → Set X} (h : ∀ i, P1 (s i)) : P1 (⋃ i, s i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have hx_closure : x ∈ closure (interior (s i)) := (h i) hx_i
  have h_subset :
      closure (interior (s i)) ⊆ closure (interior (⋃ j, s j)) := by
    apply closure_mono
    apply interior_mono
    exact Set.subset_iUnion _ i
  exact h_subset hx_closure

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P3 A) (hB : P3 B) : P3 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA_mem =>
      have hx_in : x ∈ interior (closure A) := hA hA_mem
      have h_subset : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        apply closure_mono
        exact Set.subset_union_left
      exact h_subset hx_in
  | inr hB_mem =>
      have hx_in : x ∈ interior (closure B) := hB hB_mem
      have h_subset : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        apply closure_mono
        exact Set.subset_union_right
      exact h_subset hx_in

theorem P2_iff_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A ↔ P1 A ∧ P3 A := by
  constructor
  · intro hP2
    exact ⟨P2_subset_P1 hP2, P2_subset_P3 hP2⟩
  · rintro ⟨hP1, hP3⟩
    -- We show `P2 A`.
    intro x hxA
    -- From `hP1` we obtain the equality of closures.
    have h_eq : closure (interior A) = closure A := (P1_iff_eq).1 hP1
    -- Using `hP3`, `x` lies in `interior (closure A)`.
    have hx_in : x ∈ interior (closure A) := hP3 hxA
    -- Rewriting with the equality gives the desired conclusion.
    simpa [h_eq] using hx_in

theorem P3_of_exists_dense_subset {X : Type*} [TopologicalSpace X] {A : Set X} : (∃ B, B ⊆ A ∧ closure B = Set.univ) → P3 A := by
  rintro ⟨B, hB_sub, hB_dense⟩
  intro x hxA
  -- First, deduce that `closure A = univ`.
  have hA_dense : closure A = (Set.univ : Set X) := by
    apply subset_antisymm
    · intro y hy
      trivial
    ·
      have hsubset : closure B ⊆ closure A := closure_mono hB_sub
      simpa [hB_dense] using hsubset
  -- With this, the conclusion follows immediately.
  simpa [hA_dense, interior_univ] using (Set.mem_univ x)

theorem P1_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P1 A := by
  intro x hxA
  simpa [hA.interior_eq] using (subset_closure hxA)

theorem P1_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P1 A) (hB : P1 B) : P1 (Set.prod A B) := by
  intro p hp
  rcases hp with ⟨hA_mem, hB_mem⟩
  -- `p.1` and `p.2` are in the closures of the interiors.
  have hA_cl : p.1 ∈ closure (interior A) := hA hA_mem
  have hB_cl : p.2 ∈ closure (interior B) := hB hB_mem
  -- Hence `p` is in the closure of `interior A ×ˢ interior B`.
  have h_small : p ∈ closure ((interior A) ×ˢ (interior B)) := by
    have h_prod : p ∈ (closure (interior A)) ×ˢ (closure (interior B)) :=
      ⟨hA_cl, hB_cl⟩
    simpa [closure_prod_eq] using h_prod
  -- Show that `interior A ×ˢ interior B` is contained in `interior (A.prod B)`.
  have h_subset : (interior A ×ˢ interior B) ⊆ interior (Set.prod A B) := by
    apply interior_maximal
    · intro q hq
      rcases hq with ⟨hqA, hqB⟩
      exact ⟨interior_subset hqA, interior_subset hqB⟩
    · exact (isOpen_interior).prod isOpen_interior
  -- Use monotonicity of closure to obtain the desired membership.
  have h_big : p ∈ closure (interior (Set.prod A B)) :=
    (closure_mono h_subset) h_small
  simpa using h_big

theorem P3_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P3 A) (hB : P3 B) : P3 (Set.prod A B) := by
  intro p hp
  -- `p` belongs to `A ×ˢ B`, break the hypothesis.
  rcases hp with ⟨hA_mem, hB_mem⟩
  -- Apply `P3` to each coordinate.
  have hA_int : p.1 ∈ interior (closure A) := hA hA_mem
  have hB_int : p.2 ∈ interior (closure B) := hB hB_mem
  -- `p` lies in the open rectangle below.
  have hp_small : p ∈ (interior (closure A) ×ˢ interior (closure B)) :=
    ⟨hA_int, hB_int⟩
  ----------------------------------------------------------------
  -- 1.  The rectangle is contained in `closure (A ×ˢ B)`.
  ----------------------------------------------------------------
  have h_small_subset_closure :
      (interior (closure A) ×ˢ interior (closure B)) ⊆
        closure (Set.prod A B) := by
    intro q hq
    rcases hq with ⟨hqA_int, hqB_int⟩
    have hqA_cl : q.1 ∈ closure A := interior_subset hqA_int
    have hqB_cl : q.2 ∈ closure B := interior_subset hqB_int
    have hq_mem_prod_closures : q ∈ (closure A) ×ˢ (closure B) :=
      ⟨hqA_cl, hqB_cl⟩
    -- Rewrite using `closure_prod_eq`.
    have h_eq : closure (Set.prod A B) = closure A ×ˢ closure B := by
      simpa using closure_prod_eq
    simpa [h_eq] using hq_mem_prod_closures
  ----------------------------------------------------------------
  -- 2.  Since the rectangle is open, it is contained in the interior
  --     of that closure.
  ----------------------------------------------------------------
  have h_small_subset_interior :
      (interior (closure A) ×ˢ interior (closure B)) ⊆
        interior (closure (Set.prod A B)) := by
    apply interior_maximal h_small_subset_closure
    exact (isOpen_interior).prod isOpen_interior
  ----------------------------------------------------------------
  -- 3.  Conclude that `p` lies in the required interior.
  ----------------------------------------------------------------
  exact h_small_subset_interior hp_small

theorem P2_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P2 A) (hB : P2 B) : P2 (Set.prod A B) := by
  intro p hp
  -- Decompose the point `p` and the hypothesis that it lies in `A ×ˢ B`.
  rcases hp with ⟨hA_mem, hB_mem⟩
  ----------------------------------------------------------------
  -- 1.  Apply `P2` to both coordinates.
  ----------------------------------------------------------------
  have hA_int : p.1 ∈ interior (closure (interior A)) := hA hA_mem
  have hB_int : p.2 ∈ interior (closure (interior B)) := hB hB_mem
  have hp_small :
      p ∈ (interior (closure (interior A)) ×ˢ
             interior (closure (interior B))) := by
    exact ⟨hA_int, hB_int⟩
  ----------------------------------------------------------------
  -- 2.  The rectangle above is contained in the interior of
  --     `closure (interior A ×ˢ interior B)`.
  ----------------------------------------------------------------
  have h_small_subset_closure :
      (interior (closure (interior A)) ×ˢ
        interior (closure (interior B))) ⊆
        closure (Set.prod (interior A) (interior B)) := by
    intro q hq
    rcases hq with ⟨hqA, hqB⟩
    have hqA_cl : q.1 ∈ closure (interior A) := interior_subset hqA
    have hqB_cl : q.2 ∈ closure (interior B) := interior_subset hqB
    have hq_mem : q ∈ closure (interior A) ×ˢ closure (interior B) :=
      ⟨hqA_cl, hqB_cl⟩
    have h_eq :
        closure (Set.prod (interior A) (interior B)) =
          closure (interior A) ×ˢ closure (interior B) := by
      simpa using closure_prod_eq
    simpa [h_eq] using hq_mem
  have h_small_subset_int_closure :
      (interior (closure (interior A)) ×ˢ
        interior (closure (interior B))) ⊆
        interior (closure (Set.prod (interior A) (interior B))) := by
    apply interior_maximal h_small_subset_closure
    exact (isOpen_interior).prod isOpen_interior
  ----------------------------------------------------------------
  -- 3.  Relate the two closures through monotonicity.
  ----------------------------------------------------------------
  have h_inner_subset :
      Set.prod (interior A) (interior B) ⊆ interior (Set.prod A B) := by
    apply interior_maximal
    · intro q hq
      rcases hq with ⟨hqA, hqB⟩
      exact ⟨interior_subset hqA, interior_subset hqB⟩
    · exact (isOpen_interior).prod isOpen_interior
  have h_closure_subset :
      closure (Set.prod (interior A) (interior B)) ⊆
        closure (interior (Set.prod A B)) :=
    closure_mono h_inner_subset
  have h_int_closure_subset :
      interior (closure (Set.prod (interior A) (interior B))) ⊆
        interior (closure (interior (Set.prod A B))) := by
    apply interior_mono
    exact h_closure_subset
  ----------------------------------------------------------------
  -- 4.  Combine the inclusions and finish.
  ----------------------------------------------------------------
  have h_big :
      (interior (closure (interior A)) ×ˢ
        interior (closure (interior B))) ⊆
        interior (closure (interior (Set.prod A B))) :=
    Set.Subset.trans h_small_subset_int_closure h_int_closure_subset
  exact h_big hp_small

theorem P2_product_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : P2 A) (hB : P2 B) (hC : P2 C) : P2 (Set.prod (Set.prod A B) C) := by
  exact P2_prod (P2_prod hA hB) hC

theorem P3_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : P3 A) (hB : P3 B) (hC : P3 C) : P3 (Set.prod (Set.prod A B) C) := by
  exact P3_prod (P3_prod hA hB) hC

theorem P1_univ {X : Type*} [TopologicalSpace X] : P1 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using (Set.mem_univ x)

theorem P3_empty {X : Type*} [TopologicalSpace X] : P3 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P1_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : P1 A) (hB : P1 B) (hC : P1 C) : P1 (Set.prod (Set.prod A B) C) := by
  exact P1_prod (P1_prod hA hB) hC

theorem P2_prod_four {V W X Y : Type*} [TopologicalSpace V] [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] {A : Set V} {B : Set W} {C : Set X} {D : Set Y} (hA : P2 A) (hB : P2 B) (hC : P2 C) (hD : P2 D) : P2 (Set.prod (Set.prod (Set.prod A B) C) D) := by
  exact P2_prod (P2_product_three hA hB hC) hD

theorem P3_prod_four {V W X Y : Type*} [TopologicalSpace V] [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] {A : Set V} {B : Set W} {C : Set X} {D : Set Y} (hA : P3 A) (hB : P3 B) (hC : P3 C) (hD : P3 D) : P3 (Set.prod (Set.prod (Set.prod A B) C) D) := by
  exact P3_prod (P3_prod_three hA hB hC) hD

theorem P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} : closure (interior A) = (Set.univ : Set X) → P3 A := by
  intro h_dense
  exact P2_subset_P3 (P2_of_dense_interior h_dense)

theorem P2_of_P1_and_open_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → IsOpen (closure A) → P2 A := by
  intro hP1 h_open
  -- First, build `P3 A` using the fact that `closure A` is open.
  have hP3 : P3 A := by
    intro x hxA
    have hx_closure : x ∈ closure A := subset_closure hxA
    simpa [h_open.interior_eq] using hx_closure
  -- Combine `hP1` and `hP3` via the equivalence to obtain `P2 A`.
  exact (P2_iff_P1_and_P3).2 ⟨hP1, hP3⟩

theorem P3_dense_subset {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) (hA : closure A = Set.univ) : P3 B := by
  apply P3_of_exists_dense_subset
  exact ⟨A, hAB, hA⟩

theorem P2_prod_five {U V W X Y : Type*} [TopologicalSpace U] [TopologicalSpace V] [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] {A : Set U} {B : Set V} {C : Set W} {D : Set X} {E : Set Y} (hA : P2 A) (hB : P2 B) (hC : P2 C) (hD : P2 D) (hE : P2 E) : P2 (Set.prod (Set.prod (Set.prod (Set.prod A B) C) D) E) := P2_prod (P2_prod_four hA hB hC hD) hE

theorem P2_of_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (h1 : P1 A) (h3 : P3 A) : P2 A := (P2_iff_P1_and_P3).2 ⟨h1, h3⟩

theorem P3_prod_swap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P3 (Set.prod A B) → P3 (Set.prod B A) := by
  intro hP3
  -- We must show: every point of `B ×ˢ A` lies in the interior of the closure
  -- of `B ×ˢ A`.
  intro p hp
  ----------------------------------------------------------------
  -- 1.  Apply `hP3` to the swapped point `p.swap : X × Y`.
  ----------------------------------------------------------------
  have hp_swap_mem : Prod.swap p ∈ Set.prod A B := by
    rcases hp with ⟨hpB, hpA⟩
    exact ⟨hpA, hpB⟩
  have h_int_swap : Prod.swap p ∈ interior (closure (Set.prod A B)) :=
    hP3 hp_swap_mem
  ----------------------------------------------------------------
  -- 2.  Define auxiliary sets `U` and `V`.
  ----------------------------------------------------------------
  let U : Set (X × Y) := interior (closure (Set.prod A B))
  have hU_open : IsOpen U := by
    dsimp [U]
    exact isOpen_interior
  let V : Set (Y × X) := Prod.swap ⁻¹' U
  ----------------------------------------------------------------
  -- 3.  `V` is open since `Prod.swap` is a homeomorphism.
  ----------------------------------------------------------------
  have h_cont_swap : Continuous (Prod.swap : (Y × X) → (X × Y)) :=
    (Homeomorph.prodComm Y X).continuous_toFun
  have hV_open : IsOpen V := by
    dsimp [V]
    exact h_cont_swap.isOpen_preimage (s := U) hU_open
  ----------------------------------------------------------------
  -- 4.  Our point `p` belongs to `V`.
  ----------------------------------------------------------------
  have hpV : p ∈ V := by
    dsimp [V] at *
    exact h_int_swap
  ----------------------------------------------------------------
  -- 5.  Show that `V ⊆ closure (B ×ˢ A)`.
  ----------------------------------------------------------------
  have hV_sub_closure : V ⊆ closure (Set.prod B A) := by
    intro x hxV
    -- First, get that `x.swap` lies in the closure of `A ×ˢ B`.
    have hxU : Prod.swap x ∈ U := by
      simpa [V] using hxV
    have h_swap_x_cl : Prod.swap x ∈ closure (Set.prod A B) := by
      dsimp [U] at hxU
      exact interior_subset hxU
    -- Rewrite `closure (A ×ˢ B)` as a product of closures.
    have hset1 : closure (Set.prod A B) = closure A ×ˢ closure B := by
      simpa using closure_prod_eq
    have h_coords : Prod.swap x ∈ closure A ×ˢ closure B := by
      simpa [hset1] using h_swap_x_cl
    rcases h_coords with ⟨hxA_cl, hxB_cl⟩
    -- Swap the coordinates back.
    have hx_prod : x ∈ closure B ×ˢ closure A := ⟨hxB_cl, hxA_cl⟩
    -- Turn this into the required membership.
    have hset2 : closure (Set.prod B A) = closure B ×ˢ closure A := by
      simpa using closure_prod_eq
    simpa [hset2] using hx_prod
  ----------------------------------------------------------------
  -- 6.  Since `V` is open, it is contained in the desired interior.
  ----------------------------------------------------------------
  have hV_sub_interior :
      V ⊆ interior (closure (Set.prod B A)) :=
    interior_maximal hV_sub_closure hV_open
  ----------------------------------------------------------------
  -- 7.  Conclude for the original point `p`.
  ----------------------------------------------------------------
  exact hV_sub_interior hpV

theorem P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : P1 (closure A) := by
  -- From `hA` we get an equality of closures.
  have h_eq : closure (interior A) = closure A := (P1_iff_eq).1 hA
  intro x hx
  -- Rewrite `hx` using the equality.
  have hx' : x ∈ closure (interior A) := by
    simpa [h_eq] using hx
  -- Use monotonicity of `interior` and `closure`.
  have h_subset : closure (interior A) ⊆ closure (interior (closure A)) := by
    have h_int : interior A ⊆ interior (closure A) := by
      apply interior_mono
      exact subset_closure
    exact closure_mono h_int
  -- Conclude.
  exact h_subset hx'

theorem P1_inter_closure_subset {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (interior (closure A)) := by
  intro x hx
  simpa [interior_interior] using (subset_closure hx)

theorem P1_dense_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → closure (interior A) = closure A := by
  intro hP2
  exact (P1_iff_eq).1 (P2_subset_P1 hP2)

theorem P2_prod_swap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P2 (Set.prod A B) → P2 (Set.prod B A) := by
  intro hP2
  -- `p : Y × X`, `hp : p ∈ B ×ˢ A`
  intro p hp
  ----------------------------------------------------------------
  -- 0.  A few abbreviations.
  ----------------------------------------------------------------
  set sAB : Set (X × Y) := Set.prod A B
  set sBA : Set (Y × X) := Set.prod B A
  set S₁ : Set (Y × X) := interior (closure (interior sBA))
  set S₂ : Set (X × Y) := interior (closure (interior sAB))
  -- The coordinate–swap homeomorphism   (domain `Y × X`, codomain `X × Y`).
  let e : (Y × X) ≃ₜ (X × Y) := (Homeomorph.prodComm X Y).symm
  have e_apply : (⇑e) = Prod.swap := rfl
  ----------------------------------------------------------------
  -- 1.  Apply the hypothesis `hP2` to the swapped point.
  ----------------------------------------------------------------
  have h_mem_AB : (⇑e) p ∈ sAB := by
    rcases hp with ⟨hpB, hpA⟩
    simpa [sAB, sBA, e_apply] using And.intro hpA hpB
  have h_in_AB :
      (⇑e) p ∈ interior (closure (interior sAB)) :=
    hP2 h_mem_AB
  ----------------------------------------------------------------
  -- 2.  Show that `e '' S₁ = S₂`.
  ----------------------------------------------------------------
  have h_swap_prod : (⇑e) '' sBA = sAB := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases hq with ⟨hqB, hqA⟩
      simpa [sAB, sBA, e_apply] using And.intro hqA hqB
    · intro hx
      rcases x with ⟨a, b⟩
      dsimp [sAB] at hx
      rcases hx with ⟨haA, hbB⟩
      have hq : (b, a) ∈ sBA := by
        dsimp [sBA]; exact And.intro hbB haA
      refine ⟨(b, a), hq, ?_⟩
      simp [e_apply]
  have h_image :
      (⇑e) '' S₁ = S₂ := by
    -- unfold the two sets
    dsimp [S₁, S₂]
    -- first `image_interior`
    have h1 :
        (⇑e) '' interior (closure (interior sBA)) =
          interior ((⇑e) '' closure (interior sBA)) :=
      (e.image_interior (s := closure (interior sBA)))
    -- then `image_closure`
    have h2 :
        (⇑e) '' closure (interior sBA) =
          closure ((⇑e) '' interior sBA) :=
      (e.image_closure (s := interior sBA))
    -- next `image_interior` again
    have h3 :
        (⇑e) '' interior sBA =
          interior ((⇑e) '' sBA) :=
      (e.image_interior (s := sBA))
    -- combine everything
    simpa [h2, h3, h_swap_prod] using h1
  ----------------------------------------------------------------
  -- 3.  Transport the membership back to `p`.
  ----------------------------------------------------------------
  have h_in_image :
      (⇑e) p ∈ (⇑e) '' S₁ := by
    simpa [h_image] using h_in_AB
  rcases h_in_image with ⟨q, hqS₁, h_eq⟩
  -- `e` is injective, hence `q = p`.
  have h_qp : q = p := (e.injective h_eq)
  -- Finish.
  have hpS₁ : p ∈ S₁ := by
    simpa [h_qp] using hqS₁
  simpa [S₁] using hpS₁

theorem P1_of_closure_subset {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure A ⊆ closure (interior A)) : P1 A := by
  intro x hxA
  exact h (subset_closure hxA)

theorem P1_prod_comm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P1 (Set.prod A B) ↔ P1 (Set.prod B A) := by
  constructor
  · -- `P1 (A ×ˢ B) → P1 (B ×ˢ A)`
    intro hP1
    intro p hpBA
    -- Homeomorphism that swaps the coordinates.
    let e : (Y × X) ≃ₜ (X × Y) := (Homeomorph.prodComm X Y).symm
    have e_apply : (⇑e) = Prod.swap := rfl
    ----------------------------------------------------------------
    -- 1.  Transport `p` to `A ×ˢ B` and apply `hP1`.
    ----------------------------------------------------------------
    have hpAB : (⇑e) p ∈ Set.prod A B := by
      rcases hpBA with ⟨hpB, hpA⟩
      simpa [Set.prod, e_apply] using And.intro hpA hpB
    have h_cl_AB : (⇑e) p ∈ closure (interior (Set.prod A B)) :=
      hP1 hpAB
    ----------------------------------------------------------------
    -- 2.  Relate the two closures through `e`.
    ----------------------------------------------------------------
    -- `e '' (B ×ˢ A) = A ×ˢ B`
    have h_swap_prod : (⇑e) '' (Set.prod B A) = Set.prod A B := by
      ext q
      constructor
      · rintro ⟨r, hrBA, rfl⟩
        rcases hrBA with ⟨hrB, hrA⟩
        simpa [Set.prod, e_apply] using And.intro hrA hrB
      · intro hqAB
        rcases q with ⟨a, b⟩
        dsimp [Set.prod] at hqAB
        rcases hqAB with ⟨haA, hbB⟩
        have h_pre : (b, a) ∈ Set.prod B A := by
          exact And.intro hbB haA
        refine ⟨(b, a), h_pre, ?_⟩
        simp [e_apply]
    -- `e '' interior (B ×ˢ A) = interior (A ×ˢ B)`
    have h_image_int :
        (⇑e) '' interior (Set.prod B A) = interior (Set.prod A B) := by
      have h := e.image_interior (s := Set.prod B A)
      simpa [h_swap_prod] using h
    -- `e '' closure (interior (B ×ˢ A)) = closure (interior (A ×ˢ B))`
    have h_image_cl :
        (⇑e) '' closure (interior (Set.prod B A)) =
          closure (interior (Set.prod A B)) := by
      have h := e.image_closure (s := interior (Set.prod B A))
      simpa [h_image_int] using h
    -- Use the equality to pull the membership back to `p`.
    have h_in_image :
        (⇑e) p ∈ (⇑e) '' closure (interior (Set.prod B A)) := by
      simpa [h_image_cl] using h_cl_AB
    rcases h_in_image with ⟨q, hq_cl, h_eq⟩
    have hq_eq : q = p := e.injective h_eq
    simpa [hq_eq] using hq_cl
  · -- `P1 (B ×ˢ A) → P1 (A ×ˢ B)`  (same argument with roles swapped)
    intro hP1
    intro p hpAB
    -- Homeomorphism that swaps the coordinates (opposite direction).
    let e : (X × Y) ≃ₜ (Y × X) := Homeomorph.prodComm X Y
    have e_apply : (⇑e) = Prod.swap := rfl
    ----------------------------------------------------------------
    -- 1.  Transport `p` to `B ×ˢ A` and apply `hP1`.
    ----------------------------------------------------------------
    have hpBA : (⇑e) p ∈ Set.prod B A := by
      rcases hpAB with ⟨hpA, hpB⟩
      simpa [Set.prod, e_apply] using And.intro hpB hpA
    have h_cl_BA : (⇑e) p ∈ closure (interior (Set.prod B A)) :=
      hP1 hpBA
    ----------------------------------------------------------------
    -- 2.  Relate the closures through `e`.
    ----------------------------------------------------------------
    -- `e '' (A ×ˢ B) = B ×ˢ A`
    have h_swap_prod : (⇑e) '' (Set.prod A B) = Set.prod B A := by
      ext q
      constructor
      · rintro ⟨r, hrAB, rfl⟩
        rcases hrAB with ⟨hrA, hrB⟩
        simpa [Set.prod, e_apply] using And.intro hrB hrA
      · intro hqBA
        rcases q with ⟨b, a⟩
        dsimp [Set.prod] at hqBA
        rcases hqBA with ⟨hbB, haA⟩
        have h_pre : (a, b) ∈ Set.prod A B := by
          exact And.intro haA hbB
        refine ⟨(a, b), h_pre, ?_⟩
        simp [e_apply]
    -- `e '' interior (A ×ˢ B) = interior (B ×ˢ A)`
    have h_image_int :
        (⇑e) '' interior (Set.prod A B) = interior (Set.prod B A) := by
      have h := e.image_interior (s := Set.prod A B)
      simpa [h_swap_prod] using h
    -- `e '' closure (interior (A ×ˢ B)) = closure (interior (B ×ˢ A))`
    have h_image_cl :
        (⇑e) '' closure (interior (Set.prod A B)) =
          closure (interior (Set.prod B A)) := by
      have h := e.image_closure (s := interior (Set.prod A B))
      simpa [h_image_int] using h
    -- Pull membership back.
    have h_in_image :
        (⇑e) p ∈ (⇑e) '' closure (interior (Set.prod A B)) := by
      simpa [h_image_cl] using h_cl_BA
    rcases h_in_image with ⟨q, hq_cl, h_eq⟩
    have hq_eq : q = p := e.injective h_eq
    simpa [hq_eq] using hq_cl

theorem P1_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : P1 A := by
  classical
  by_cases hA_empty : (A : Set X) = ∅
  · -- If `A` is empty, we use the lemma `P1_empty`.
    simpa [hA_empty] using (P1_empty (X := X))
  · -- Otherwise, `A` is non-empty.
    -- Obtain an element `x0 ∈ A`.
    have h_nonempty : (A : Set X).Nonempty := by
      have : (A : Set X) ≠ ∅ := hA_empty
      exact (Set.nonempty_iff_ne_empty).mpr this
    rcases h_nonempty with ⟨x0, hx0A⟩
    -- In a subsingleton type every element equals `x0`, hence `A = univ`.
    have hA_univ : (A : Set X) = Set.univ := by
      ext y
      constructor
      · intro _; simp
      · intro _
        have h_eq : y = x0 := Subsingleton.elim _ _
        simpa [h_eq] using hx0A
    -- Conclude using `P1_univ`.
    simpa [hA_univ] using (P1_univ (X := X))

theorem P1_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (e : X ≃ₜ Y) (hA : P1 A) : P1 (e '' A) := by
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` lies in `A`, hence in `closure (interior A)`.
  have hx_cl : x ∈ closure (interior A) := hA hxA
  -- Apply `e` to obtain a membership in the image of that closure.
  have h1 : e x ∈ (⇑e) '' closure (interior A) := ⟨x, hx_cl, rfl⟩
  -- Relate this image to the closure of the image of `interior A`.
  have h_image_closure :
      (⇑e) '' closure (interior A) =
        closure ((⇑e) '' interior A) := by
    simpa using e.image_closure (s := interior A)
  -- Relate the image of `interior A` to the interior of the image of `A`.
  have h_image_interior :
      (⇑e) '' interior A =
        interior ((⇑e) '' A) := by
    simpa using e.image_interior (s := A)
  -- Assemble the pieces.
  have : e x ∈ closure (interior ((⇑e) '' A)) := by
    have : e x ∈ closure ((⇑e) '' interior A) := by
      simpa [h_image_closure] using h1
    simpa [h_image_interior] using this
  simpa using this

theorem P2_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : P2 A := by
  classical
  by_cases hA_empty : (A : Set X) = ∅
  · simpa [hA_empty] using (P2_empty (X := X))
  ·
    have h_nonempty : (A : Set X).Nonempty :=
      (Set.nonempty_iff_ne_empty).mpr hA_empty
    rcases h_nonempty with ⟨x0, hx0A⟩
    have hA_univ : (A : Set X) = Set.univ := by
      ext y
      constructor
      · intro _; simp
      · intro _
        have h_eq : y = x0 := Subsingleton.elim _ _
        simpa [h_eq] using hx0A
    simpa [hA_univ] using (P2_univ (X := X))

theorem P1_empty_iff {X : Type*} [TopologicalSpace X] : P1 (∅ : Set X) ↔ True := by
  simpa using (iff_true_intro (P1_empty (X := X)))

theorem P3_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} (hA : P3 A) : P3 (e '' A) := by
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` is in the interior of `closure A`.
  have hx_int : x ∈ interior (closure A) := hA hxA
  -- Apply `e` to get a membership in the image.
  have h1 : e x ∈ (⇑e) '' interior (closure A) := ⟨x, hx_int, rfl⟩
  -- Use `e.image_interior` to rewrite.
  have h2 : e x ∈ interior ((⇑e) '' closure A) := by
    have h_eq := e.image_interior (s := closure A)
    simpa [h_eq] using h1
  -- Use `e.image_closure` to rewrite once more.
  have h3 : e x ∈ interior (closure ((⇑e) '' A)) := by
    have h_eq := e.image_closure (s := A)
    simpa [h_eq] using h2
  simpa using h3

theorem P1_prod_left_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : P1 A) : P1 (Set.prod A (Set.univ : Set Y)) := by
  have h_univ : P1 (Set.univ : Set Y) := P1_univ (X := Y)
  simpa using P1_prod hA h_univ

theorem P2_prod_left_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : P2 A) : P2 (Set.prod A (Set.univ : Set Y)) := by
  have h_univ : P2 (Set.univ : Set Y) := P2_univ (X := Y)
  simpa using P2_prod hA h_univ

theorem P3_prod_left_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : P3 A) : P3 (Set.prod A (Set.univ : Set Y)) := by
  have h_univ : P3 (Set.univ : Set Y) := P3_univ (X := Y)
  simpa using P3_prod hA h_univ

theorem P2_iff_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (h_open : IsOpen A) : P2 A ↔ P3 A := by
  have hP1 : P1 A := P1_open h_open
  have h_equiv := (P2_iff_P1_and_P3 (A := A))
  constructor
  · intro hP2
    exact (h_equiv.1 hP2).2
  · intro hP3
    exact h_equiv.2 ⟨hP1, hP3⟩

theorem P3_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : P3 A := by
  exact (P2_subset_P3 (A := A)) (P2_subsingleton (A := A))

theorem P3_iff_P2_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (h_closed : IsClosed A) : P3 A ↔ P2 A := by
  constructor
  · intro hP3
    -- First show `P1 A` using `hP3` and the fact that `A` is closed.
    have hP1 : P1 A := by
      intro x hxA
      -- From `hP3` we have `x ∈ interior (closure A)`, but `closure A = A`.
      have hx_intA : x ∈ interior A := by
        have : x ∈ interior (closure A) := hP3 hxA
        simpa [h_closed.closure_eq] using this
      -- `interior A ⊆ closure (interior A)` by `subset_closure`.
      exact subset_closure hx_intA
    -- Combine `hP1` and `hP3` via the equivalence to obtain `P2 A`.
    exact (P2_iff_P1_and_P3).2 ⟨hP1, hP3⟩
  · -- The converse direction is immediate from `P2 ⟶ P3`.
    intro hP2
    exact P2_subset_P3 hP2

theorem P3_neq {X : Type*} [TopologicalSpace X] {A : Set X} : ¬ P3 A → interior (closure A) ≠ closure A := by
  intro hNotP3
  intro h_eq
  -- From the assumed equality we can build `P3 A`.
  have hP3 : P3 A := by
    intro x hxA
    have hx_closure : x ∈ closure A := subset_closure hxA
    simpa [h_eq] using hx_closure
  -- This contradicts the assumption `¬ P3 A`.
  exact hNotP3 hP3

theorem P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (interior A) := by
  exact P2_subset_P1 (P2_self (A := A))

theorem P2_prod_comm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P2 (Set.prod A B) ↔ P2 (Set.prod B A) := by
  constructor
  · intro hAB
    exact P2_prod_swap (A := A) (B := B) hAB
  · intro hBA
    exact (P2_prod_swap (X := Y) (Y := X) (A := B) (B := A)) hBA

theorem P1_prod_right_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} : P1 B → P1 (Set.prod (Set.univ : Set X) B) := by
  intro hB
  have h_univ : P1 (Set.univ : Set X) := P1_univ (X := X)
  simpa using P1_prod h_univ hB

theorem P2_prod_right_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} : P2 B → P2 (Set.prod (Set.univ : Set X) B) := by
  intro hB
  have h_univ : P2 (Set.univ : Set X) := P2_univ (X := X)
  simpa using P2_prod h_univ hB

theorem P3_prod_right_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} : P3 B → P3 (Set.prod (Set.univ : Set X) B) := by
  intro hB
  have h_univ : P3 (Set.univ : Set X) := P3_univ (X := X)
  simpa using P3_prod h_univ hB

theorem P1_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} : P1 B → P1 (e ⁻¹' B) := by
  intro hB
  intro x hx
  -- `hx` gives that `e x ∈ B`.
  have hxB : (e x) ∈ B := hx
  -- Apply `P1` for `B`.
  have h_closure : (e x) ∈ closure (interior B) := hB hxB
  ----------------------------------------------------------------
  -- 1.  Transport the membership with `e.symm`.
  ----------------------------------------------------------------
  have h_in_image : x ∈ (⇑(e.symm)) '' closure (interior B) := by
    refine ⟨e x, h_closure, ?_⟩
    simp
  -- Rewrite the image of the closure.
  have h_image_cl :
      (⇑(e.symm)) '' closure (interior B) =
        closure ((⇑(e.symm)) '' interior B) := by
    simpa using e.symm.image_closure (s := interior B)
  have h_in_closure_image :
      x ∈ closure ((⇑(e.symm)) '' interior B) := by
    have : x ∈ (⇑(e.symm)) '' closure (interior B) := h_in_image
    simpa [h_image_cl] using this
  ----------------------------------------------------------------
  -- 2.  Relate the two interiors.
  ----------------------------------------------------------------
  -- First, identify `e.symm '' B` with the preimage `e ⁻¹' B`.
  have h_image_pre :
      (⇑(e.symm)) '' B = (e ⁻¹' B) := by
    ext y
    constructor
    · rintro ⟨b, hbB, rfl⟩
      simpa [e.apply_symm_apply] using hbB
    · intro hy
      refine ⟨e y, hy, ?_⟩
      simp
  -- Now rewrite the image of the interior.
  have h_image_int :
      (⇑(e.symm)) '' interior B = interior (e ⁻¹' B) := by
    have h := e.symm.image_interior (s := B)
    simpa [h_image_pre] using h
  ----------------------------------------------------------------
  -- 3.  Conclude.
  ----------------------------------------------------------------
  have : x ∈ closure (interior (e ⁻¹' B)) := by
    have : x ∈ closure ((⇑(e.symm)) '' interior B) := h_in_closure_image
    simpa [h_image_int] using this
  exact this

theorem P2_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} : P2 B → P2 (e ⁻¹' B) := by
  intro hB
  intro x hx
  -- `hx` tells us that `e x ∈ B`.
  have hxB : e x ∈ B := hx
  -- Apply `P2` for `B`.
  have h_mem : e x ∈ interior (closure (interior B)) := hB hxB
  ----------------------------------------------------------------
  -- 1.  Transport the membership with `e.symm`.
  ----------------------------------------------------------------
  have h_img :
      x ∈ (e.symm) '' interior (closure (interior B)) := by
    exact ⟨e x, h_mem, by
      simpa using (e.symm_apply_apply x)⟩
  -- Rewrite the image of an interior.
  have h_step1 :
      x ∈ interior ((e.symm) '' closure (interior B)) := by
    have h_eq :=
      e.symm.image_interior (s := closure (interior B))
    simpa [h_eq] using h_img
  -- Rewrite the image of a closure.
  have h_step2 :
      x ∈ interior (closure ((e.symm) '' interior B)) := by
    have h_eq := e.symm.image_closure (s := interior B)
    simpa [h_eq] using h_step1
  -- Rewrite the image of an interior once more.
  have h_step3 :
      x ∈ interior (closure (interior ((e.symm) '' B))) := by
    have h_eq := e.symm.image_interior (s := B)
    simpa [h_eq] using h_step2
  ----------------------------------------------------------------
  -- 2.  Identify `(e.symm) '' B` with the pre-image `e ⁻¹' B`.
  ----------------------------------------------------------------
  have h_image_pre : (e.symm) '' B = (e ⁻¹' B) := by
    ext y
    constructor
    · rintro ⟨b, hbB, rfl⟩
      simpa using hbB
    · intro hy
      exact ⟨e y, hy, by simp⟩
  ----------------------------------------------------------------
  -- 3.  Conclude.
  ----------------------------------------------------------------
  simpa [h_image_pre] using h_step3

theorem P3_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} : P3 B → P3 (e ⁻¹' B) := by
  intro hB
  intro x hx
  have hxB : e x ∈ B := hx
  -- Step 1: use `hB`.
  have h_int : e x ∈ interior (closure B) := hB hxB
  -- Step 2: transport with `e.symm`.
  have h1 : x ∈ (e.symm) '' interior (closure B) := by
    refine ⟨e x, h_int, ?_⟩
    simp
  -- Rewrite the image of an interior.
  have h2 : x ∈ interior ((e.symm) '' closure B) := by
    simpa [e.symm.image_interior (s := closure B)] using h1
  -- Rewrite the image of a closure.
  have h3 : x ∈ interior (closure ((e.symm) '' B)) := by
    simpa [e.symm.image_closure (s := B)] using h2
  -- Identify the image with the preimage.
  have h_image_pre : (e.symm) '' B = (e ⁻¹' B) := by
    ext y
    constructor
    · rintro ⟨b, hbB, rfl⟩
      simpa using hbB
    · intro hy
      refine ⟨e y, hy, ?_⟩
      simp
  -- Conclude.
  simpa [h_image_pre] using h3

theorem P1_Union_finite {X : Type*} [TopologicalSpace X] {A : Finset (Set X)} (h : ∀ s ∈ A, P1 s) : P1 (⋃ s ∈ A, s) := by
  classical
  intro x hx
  -- Extract the witness set `S` with `S ∈ A` and `x ∈ S`.
  rcases Set.mem_iUnion.1 hx with ⟨S, hx⟩
  rcases Set.mem_iUnion.1 hx with ⟨hS_mem, hxS⟩
  -- Apply the hypothesis `h` to `S`.
  have hx_cl : x ∈ closure (interior S) := (h S hS_mem) hxS
  -- `S` is contained in the big union, hence so is `interior S`.
  have hS_subset :
      S ⊆ ⋃ T ∈ (A : Set (Set X)), (T : Set X) := by
    intro y hy
    refine Set.mem_iUnion.2 ⟨S, ?_⟩
    refine Set.mem_iUnion.2 ⟨hS_mem, hy⟩
  -- Monotonicity of `interior` and `closure`.
  have h_subset :
      closure (interior S) ⊆
        closure (interior (⋃ T ∈ (A : Set (Set X)), (T : Set X))) := by
    apply closure_mono
    apply interior_mono
    exact hS_subset
  exact h_subset hx_cl

theorem P2_Union_finite {X : Type*} [TopologicalSpace X] {A : Finset (Set X)} (h : ∀ s ∈ A, P2 s) : P2 (⋃ s ∈ A, s) := by
  classical
  intro x hx
  -- Find the particular set `S` of the finite union that contains `x`.
  rcases Set.mem_iUnion.1 hx with ⟨S, hx⟩
  rcases Set.mem_iUnion.1 hx with ⟨hS_mem, hxS⟩
  -- Apply `P2` to `S`.
  have hx_in : x ∈ interior (closure (interior S)) := (h S hS_mem) hxS
  -- `S` is contained in the whole union.
  have hS_subset :
      (S : Set X) ⊆ ⋃ T ∈ (A : Set (Set X)), (T : Set X) := by
    intro y hy
    apply Set.mem_iUnion.2
    refine ⟨S, ?_⟩
    apply Set.mem_iUnion.2
    exact ⟨hS_mem, hy⟩
  -- Monotonicity of `interior` and `closure` gives the desired inclusion.
  have h_subset :
      interior (closure (interior S)) ⊆
        interior (closure (interior (⋃ T ∈ (A : Set (Set X)), (T : Set X)))) := by
    apply interior_mono
    apply closure_mono
    apply interior_mono
    exact hS_subset
  exact h_subset hx_in

theorem P1_P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (h_open : IsOpen A) : P1 A ↔ P2 A := by
  constructor
  · intro _hP1
    exact P2_open h_open
  · intro _hP2
    exact P1_open h_open

theorem P1_dense_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} (h_dense : closure (interior A) = Set.univ) : closure (interior (e '' A)) = Set.univ := by
  -- Step 1: relate the two closures through the homeomorphism `e`.
  have h1 : closure (interior (e '' A)) = (⇑e) '' closure (interior A) := by
    -- `e.image_closure` gives the image of a closure,
    -- `e.image_interior` the image of an interior.
    have h_cl : (⇑e) '' closure (interior A) =
        closure ((⇑e) '' interior A) := by
      simpa using e.image_closure (s := interior A)
    have h_int : (⇑e) '' interior A = interior (e '' A) := by
      simpa using e.image_interior (s := A)
    simpa [h_int] using h_cl.symm
  -- Step 2: use the density hypothesis.
  have h2 : closure (interior (e '' A)) = (⇑e) '' (Set.univ : Set X) := by
    simpa [h_dense] using h1
  -- Step 3: the image of `univ` under a surjective map is `univ`.
  have h3 : (⇑e) '' (Set.univ : Set X) = (Set.univ : Set Y) := by
    ext y
    constructor
    · intro _; trivial
    · intro _; rcases e.surjective y with ⟨x, rfl⟩; exact ⟨x, trivial, rfl⟩
  -- Step 4: conclude.
  simpa [h3] using h2

theorem P1_prod_distrib {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : P1 A) (hBC : P1 (Set.prod B C)) : P1 (Set.prod (Set.prod A B) C) := by
  classical
  ----------------------------------------------------------------
  -- 1.  First build `P1` for `A ×ˢ (B ×ˢ C)`.
  ----------------------------------------------------------------
  have hABC : P1 (Set.prod A (Set.prod B C)) := P1_prod hA hBC
  ----------------------------------------------------------------
  -- 2.  Transport this property with the associativity homeomorphism
  --     `(X × (Y × Z)) ≃ ((X × Y) × Z)`.
  ----------------------------------------------------------------
  let e : (X × (Y × Z)) ≃ₜ ((X × Y) × Z) :=
    (Homeomorph.prodAssoc X Y Z).symm
  have hImage : P1 (e '' Set.prod A (Set.prod B C)) :=
    P1_image_homeomorph e hABC
  ----------------------------------------------------------------
  -- 3.  Identify the image with `(A ×ˢ B) ×ˢ C`.
  ----------------------------------------------------------------
  have h_eq :
      (e '' Set.prod A (Set.prod B C)) = Set.prod (Set.prod A B) C := by
    ext p
    constructor
    · -- `→`
      rintro ⟨q, hq, rfl⟩
      --  `q : X × (Y × Z)`
      rcases q with ⟨a, bc⟩
      rcases bc with ⟨b, c⟩
      rcases hq with ⟨ha, hbc⟩
      rcases hbc with ⟨hb, hc⟩
      --  Unfold the map `e` and the definition of `Set.prod`.
      dsimp [e, Homeomorph.prodAssoc, Set.prod] at *
      exact And.intro (And.intro ha hb) hc
    · -- `←`
      intro hp
      --  Decompose `p` and the membership hypothesis.
      rcases p with ⟨⟨a, b⟩, c⟩
      dsimp [Set.prod] at hp
      rcases hp with ⟨hab, hc⟩
      rcases hab with ⟨ha, hb⟩
      --  Build the pre-image point and the required witnesses.
      refine ⟨(a, (b, c)), ?_, ?_⟩
      · dsimp [Set.prod]
        exact And.intro ha (And.intro hb hc)
      · simp [e, Homeomorph.prodAssoc]
  ----------------------------------------------------------------
  -- 4.  Rewrite with the identified equality and conclude.
  ----------------------------------------------------------------
  simpa [h_eq] using hImage

theorem P3_of_closed_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X} (h_closed : IsClosed A) (h_eq : interior A = A) : P3 A := by
  -- Since `interior A = A`, the set `A` is open.
  have h_open : IsOpen A := by
    simpa [h_eq] using (isOpen_interior : IsOpen (interior A))
  -- Apply the lemma for open sets.
  exact P3_open h_open

theorem P3_Union_dense {X : Type*} [TopologicalSpace X] {ι : Sort*} {s : ι → Set X} : (∀ i, closure (s i) = Set.univ) → P3 (⋃ i, s i) := by
  intro h
  apply P3_iUnion
  intro i
  exact P3_of_dense (h i)

theorem P2_equiv_P1_closure_open {X : Type*} [TopologicalSpace X] {A : Set X} (h_open : IsOpen (closure A)) : P2 A ↔ P1 A := by
  constructor
  · intro hP2
    exact P2_subset_P1 (A := A) hP2
  · intro hP1
    exact P2_of_P1_and_open_closure (A := A) hP1 h_open

theorem P3_Union_finite {X : Type*} [TopologicalSpace X] {A : Finset (Set X)} (h : ∀ s ∈ A, P3 s) : P3 (⋃ s ∈ A, s) := by
  classical
  intro x hx
  -- Extract a set `S ∈ A` such that `x ∈ S`.
  rcases Set.mem_iUnion.1 hx with ⟨S, hx₁⟩
  rcases Set.mem_iUnion.1 hx₁ with ⟨hS_mem, hxS⟩
  -- Use the hypothesis `P3 S`.
  have hx_int : x ∈ interior (closure S) := (h S hS_mem) hxS
  -- `S` is included in the big union.
  have hS_subset :
      (S : Set X) ⊆ ⋃ T ∈ (A : Set (Set X)), (T : Set X) := by
    intro y hy
    apply Set.mem_iUnion.2
    refine ⟨S, ?_⟩
    apply Set.mem_iUnion.2
    exact ⟨hS_mem, hy⟩
  -- Monotonicity of `closure` and `interior`.
  have h_subset :
      interior (closure S) ⊆
        interior (closure (⋃ T ∈ (A : Set (Set X)), (T : Set X))) := by
    apply interior_mono
    apply closure_mono
    exact hS_subset
  exact h_subset hx_int

theorem P1_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (closure (interior A)) := by
  intro x hx
  -- We exhibit the required inclusion between the two closures.
  have h_subset :
      closure (interior A) ⊆
        closure (interior (closure (interior A))) := by
    -- First, show the inclusion for the interiors.
    have h_int :
        interior A ⊆ interior (closure (interior A)) := by
      apply interior_maximal
      · exact subset_closure
      · exact isOpen_interior
    -- Take closures on both sides.
    exact closure_mono h_int
  -- Apply the inclusion to the given point.
  exact h_subset hx

theorem P2_of_P3_and_closed {X : Type*} [TopologicalSpace X] {A : Set X} (h_closed : IsClosed A) : P3 A → P2 A := by
  exact (P3_iff_P2_of_closed (X := X) (A := A) h_closed).1

theorem P2_prod_assoc {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : P2 (Set.prod (Set.prod A B) C) ↔ P2 (Set.prod A (Set.prod B C)) := by
  -- Abbreviate the two sets that appear in the statement.
  let S₁ : Set ((X × Y) × Z) := Set.prod (Set.prod A B) C
  let S₂ : Set (X × (Y × Z)) := Set.prod A (Set.prod B C)
  -- The associativity homeomorphism
  let e : ((X × Y) × Z) ≃ₜ (X × (Y × Z)) := Homeomorph.prodAssoc X Y Z
  ----------------------------------------------------------------
  -- 1.  Forward implication.
  ----------------------------------------------------------------
  have h_forward : P2 S₁ → P2 S₂ := by
    intro hS₁
    -- Transport the property with `e.symm`.
    have h_pre : P2 (e.symm ⁻¹' S₁) :=
      P2_preimage_homeomorph (e.symm) hS₁
    -- Identify the pre-image with `S₂`.
    have h_eq_pre : (e.symm ⁻¹' S₁) = S₂ := by
      --------------------------------------------------------------
      -- 1.1  First relate the pre-image to an image.
      --------------------------------------------------------------
      have h_step1 : (e.symm ⁻¹' S₁) = (⇑e) '' S₁ := by
        ext p
        constructor
        · intro hp
          exact ⟨e.symm p, hp, by
            simp⟩
        · rintro ⟨q, hq, rfl⟩
          simpa using hq
      --------------------------------------------------------------
      -- 1.2  Compute that image explicitly.
      --------------------------------------------------------------
      have h_step2 : (⇑e) '' S₁ = S₂ := by
        ext p
        constructor
        · rintro ⟨q, hq, rfl⟩
          -- `q : ((X × Y) × Z)` with `q ∈ S₁`
          rcases q with ⟨⟨a, b⟩, c⟩
          dsimp [S₁] at hq
          rcases hq with ⟨hab, hc⟩
          rcases hab with ⟨ha, hb⟩
          dsimp [e, Homeomorph.prodAssoc, S₂, Set.prod]
          exact And.intro ha (And.intro hb hc)
        · intro hp
          rcases p with ⟨a, bc⟩
          rcases bc with ⟨b, c⟩
          dsimp [S₂] at hp
          rcases hp with ⟨ha, hbc⟩
          rcases hbc with ⟨hb, hc⟩
          refine ⟨((a, b), c), ?_, ?_⟩
          · dsimp [S₁]
            exact And.intro (And.intro ha hb) hc
          · simp [e, Homeomorph.prodAssoc]
      --------------------------------------------------------------
      -- 1.3  Assemble the pieces.
      --------------------------------------------------------------
      simpa [h_step1, h_step2]
    -- Re-interpret `h_pre` with the identified set.
    simpa [h_eq_pre] using h_pre
  ----------------------------------------------------------------
  -- 2.  Backward implication.
  ----------------------------------------------------------------
  have h_backward : P2 S₂ → P2 S₁ := by
    intro hS₂
    -- Transport the property with `e`.
    have h_pre : P2 (e ⁻¹' S₂) :=
      P2_preimage_homeomorph e hS₂
    -- Identify the pre-image with `S₁`.
    have h_eq_pre : (e ⁻¹' S₂) = S₁ := by
      ext p
      change (⇑e p ∈ S₂) ↔ (p ∈ S₁)
      constructor
      · intro hp
        rcases p with ⟨⟨a, b⟩, c⟩
        dsimp [e, Homeomorph.prodAssoc] at hp
        dsimp [S₂] at hp
        rcases hp with ⟨ha, hbc⟩
        rcases hbc with ⟨hb, hc⟩
        dsimp [S₁]
        exact And.intro (And.intro ha hb) hc
      · intro hp
        rcases p with ⟨⟨a, b⟩, c⟩
        dsimp [S₁] at hp
        rcases hp with ⟨hab, hc⟩
        rcases hab with ⟨ha, hb⟩
        dsimp [e, Homeomorph.prodAssoc, S₂]
        exact And.intro ha (And.intro hb hc)
    simpa [h_eq_pre] using h_pre
  ----------------------------------------------------------------
  -- 3.  Conclude.
  ----------------------------------------------------------------
  simpa [S₁, S₂] using (⟨h_forward, h_backward⟩)

theorem P1_prod_assoc {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : P1 (Set.prod (Set.prod A B) C) ↔ P1 (Set.prod A (Set.prod B C)) := by
  -- Abbreviate the two sets that appear in the statement.
  let S₁ : Set ((X × Y) × Z) := Set.prod (Set.prod A B) C
  let S₂ : Set (X × (Y × Z)) := Set.prod A (Set.prod B C)
  -- The associativity homeomorphism `( (X × Y) × Z ) ≃ ( X × (Y × Z) )`.
  let e : ((X × Y) × Z) ≃ₜ (X × (Y × Z)) := Homeomorph.prodAssoc X Y Z
  ----------------------------------------------------------------
  -- 1.  Forward implication.
  ----------------------------------------------------------------
  have h_forward : P1 S₁ → P1 S₂ := by
    intro hS₁
    -- Transport the property through the homeomorphism `e`.
    have h_img : P1 (e '' S₁) := P1_image_homeomorph e hS₁
    -- Identify the image with `S₂`.
    have h_eq : (e '' S₁) = S₂ := by
      ext p
      constructor
      · rintro ⟨q, hq, rfl⟩
        --  `q : ((X × Y) × Z)` and `hq : q ∈ S₁`.
        rcases q with ⟨⟨a, b⟩, c⟩
        dsimp [S₁, Set.prod] at hq
        rcases hq with ⟨hab, hc⟩
        rcases hab with ⟨ha, hb⟩
        --  Show membership in `S₂`.
        dsimp [e, Homeomorph.prodAssoc, S₂, Set.prod]
        exact And.intro ha (And.intro hb hc)
      · intro hp
        --  Decompose `p : X × (Y × Z)`.
        rcases p with ⟨a, bc⟩
        rcases bc with ⟨b, c⟩
        dsimp [S₂, Set.prod] at hp
        rcases hp with ⟨ha, hbc⟩
        rcases hbc with ⟨hb, hc⟩
        --  Build the pre-image point and witnesses.
        refine ⟨((a, b), c), ?_, ?_⟩
        · dsimp [S₁, Set.prod]
          exact And.intro (And.intro ha hb) hc
        · simp [e, Homeomorph.prodAssoc]
    simpa [h_eq] using h_img
  ----------------------------------------------------------------
  -- 2.  Backward implication.
  ----------------------------------------------------------------
  have h_backward : P1 S₂ → P1 S₁ := by
    intro hS₂
    -- Transport the property through the inverse homeomorphism `e.symm`.
    have h_img : P1 (e.symm '' S₂) := P1_image_homeomorph e.symm hS₂
    -- Identify this image with `S₁`.
    have h_eq : (e.symm '' S₂) = S₁ := by
      ext p
      constructor
      · rintro ⟨q, hq, rfl⟩
        --  `q : X × (Y × Z)` and `hq : q ∈ S₂`.
        rcases q with ⟨a, bc⟩
        rcases bc with ⟨b, c⟩
        dsimp [S₂, Set.prod] at hq
        rcases hq with ⟨ha, hbc⟩
        rcases hbc with ⟨hb, hc⟩
        --  Show membership in `S₁`.
        dsimp [e, Homeomorph.prodAssoc, S₁, Set.prod]
        exact And.intro (And.intro ha hb) hc
      · intro hp
        --  Decompose `p : ((X × Y) × Z)`.
        rcases p with ⟨⟨a, b⟩, c⟩
        dsimp [S₁, Set.prod] at hp
        rcases hp with ⟨hab, hc⟩
        rcases hab with ⟨ha, hb⟩
        --  Build the pre-image point and witnesses.
        refine ⟨(a, (b, c)), ?_, ?_⟩
        · dsimp [S₂, Set.prod]
          exact And.intro ha (And.intro hb hc)
        · simp [e, Homeomorph.prodAssoc]
    simpa [h_eq] using h_img
  ----------------------------------------------------------------
  -- 3.  Conclude.
  ----------------------------------------------------------------
  simpa [S₁, S₂] using (Iff.intro h_forward h_backward)

theorem P3_prod_assoc {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : P3 (Set.prod (Set.prod A B) C) ↔ P3 (Set.prod A (Set.prod B C)) := by
  -- Abbreviate the two sets that appear in the statement.
  let S₁ : Set ((X × Y) × Z) := Set.prod (Set.prod A B) C
  let S₂ : Set (X × (Y × Z)) := Set.prod A (Set.prod B C)
  -- The associativity homeomorphism `( (X × Y) × Z ) ≃ ( X × (Y × Z) )`.
  let e : ((X × Y) × Z) ≃ₜ (X × (Y × Z)) := Homeomorph.prodAssoc X Y Z
  ----------------------------------------------------------------
  -- 1.  Forward implication.
  ----------------------------------------------------------------
  have h_forward : P3 S₁ → P3 S₂ := by
    intro hS₁
    -- Transport the property through the homeomorphism `e`.
    have h_img : P3 (e '' S₁) := P3_image_homeomorph e hS₁
    -- Identify the image with `S₂`.
    have h_eq : (e '' S₁) = S₂ := by
      ext p
      constructor
      · rintro ⟨q, hq, rfl⟩
        --  `q : ((X × Y) × Z)` and `hq : q ∈ S₁`.
        rcases q with ⟨⟨a, b⟩, c⟩
        dsimp [S₁, Set.prod] at hq
        rcases hq with ⟨hab, hc⟩
        rcases hab with ⟨ha, hb⟩
        --  Show membership in `S₂`.
        dsimp [e, Homeomorph.prodAssoc, S₂, Set.prod]
        exact And.intro ha (And.intro hb hc)
      · intro hp
        --  Decompose `p : X × (Y × Z)`.
        rcases p with ⟨a, bc⟩
        rcases bc with ⟨b, c⟩
        dsimp [S₂, Set.prod] at hp
        rcases hp with ⟨ha, hbc⟩
        rcases hbc with ⟨hb, hc⟩
        --  Build the pre-image point and witnesses.
        refine ⟨((a, b), c), ?_, ?_⟩
        · dsimp [S₁, Set.prod]
          exact And.intro (And.intro ha hb) hc
        · simp [e, Homeomorph.prodAssoc]
    simpa [h_eq] using h_img
  ----------------------------------------------------------------
  -- 2.  Backward implication.
  ----------------------------------------------------------------
  have h_backward : P3 S₂ → P3 S₁ := by
    intro hS₂
    -- Transport the property through the inverse homeomorphism `e.symm`.
    have h_img : P3 (e.symm '' S₂) := P3_image_homeomorph e.symm hS₂
    -- Identify this image with `S₁`.
    have h_eq : (e.symm '' S₂) = S₁ := by
      ext p
      constructor
      · rintro ⟨q, hq, rfl⟩
        --  `q : X × (Y × Z)` and `hq : q ∈ S₂`.
        rcases q with ⟨a, bc⟩
        rcases bc with ⟨b, c⟩
        dsimp [S₂, Set.prod] at hq
        rcases hq with ⟨ha, hbc⟩
        rcases hbc with ⟨hb, hc⟩
        --  Show membership in `S₁`.
        dsimp [e, Homeomorph.prodAssoc, S₁, Set.prod]
        exact And.intro (And.intro ha hb) hc
      · intro hp
        --  Decompose `p : ((X × Y) × Z)`.
        rcases p with ⟨⟨a, b⟩, c⟩
        dsimp [S₁, Set.prod] at hp
        rcases hp with ⟨hab, hc⟩
        rcases hab with ⟨ha, hb⟩
        --  Build the pre-image point and witnesses.
        refine ⟨(a, (b, c)), ?_, ?_⟩
        · dsimp [S₂, Set.prod]
          exact And.intro ha (And.intro hb hc)
        · simp [e, Homeomorph.prodAssoc]
    simpa [h_eq] using h_img
  ----------------------------------------------------------------
  -- 3.  Conclude.
  ----------------------------------------------------------------
  simpa [S₁, S₂] using (Iff.intro h_forward h_backward)

theorem P1_prod_distrib_right {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hAB : P1 (Set.prod A B)) (hC : P1 C) : P1 (Set.prod A (Set.prod B C)) := by
  -- Step 1: obtain `P1` for `(A ×ˢ B) ×ˢ C`.
  have h₁ : P1 (Set.prod (Set.prod A B) C) := P1_prod hAB hC
  -- Step 2: use associativity of the product to transfer the property.
  have h₂ : P1 (Set.prod A (Set.prod B C)) :=
    (P1_prod_assoc (A := A) (B := B) (C := C)).1 h₁
  simpa using h₂

theorem P2_prod_distrib_right {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hAB : P2 (Set.prod A B)) (hC : P2 C) : P2 (Set.prod A (Set.prod B C)) := by
  -- First, obtain `P2` for `(A ×ˢ B) ×ˢ C`.
  have h₁ : P2 (Set.prod (Set.prod A B) C) := P2_prod hAB hC
  -- Use associativity of the product to transport the property.
  have h₂ : P2 (Set.prod A (Set.prod B C)) :=
    (P2_prod_assoc (A := A) (B := B) (C := C)).1 h₁
  simpa using h₂

theorem P3_prod_distrib_right {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hAB : P3 (Set.prod A B)) (hC : P3 C) : P3 (Set.prod A (Set.prod B C)) := by
  -- First, obtain `P3` for `(A ×ˢ B) ×ˢ C`.
  have h₁ : P3 (Set.prod (Set.prod A B) C) := P3_prod hAB hC
  -- Use associativity of the product to transport the property.
  have h₂ : P3 (Set.prod A (Set.prod B C)) :=
    (P3_prod_assoc (A := A) (B := B) (C := C)).1 h₁
  simpa using h₂

theorem P1_Union_dense {X : Type*} [TopologicalSpace X] {ι : Sort*} {s : ι → Set X} (h : ∀ i, closure (interior (s i)) = Set.univ) : P1 (⋃ i, s i) := by
  -- First, turn the density assumption into `P1` for each individual set.
  have hP1 : ∀ i, P1 (s i) :=
    fun i => P1_of_dense_interior (X := X) (A := s i) (h i)
  -- Then apply the `P1`-closure under arbitrary unions.
  exact P1_iUnion hP1

theorem P3_dense_range {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) (hf : DenseRange f) : P3 (Set.range f) := by
  exact
    P3_of_dense (A := Set.range f) (by
      simpa using hf.closure_eq)

theorem P1_prod_empty {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : P1 (Set.prod A (∅ : Set Y)) := by
  intro p hp
  rcases hp with ⟨_, hB⟩
  have hFalse : False := by
    simpa [Set.mem_empty_iff_false] using hB
  exact hFalse.elim

theorem P2_prod_empty {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : P2 (Set.prod A (∅ : Set Y)) := by
  intro p hp
  have hFalse : False := by
    rcases hp with ⟨_, hB⟩
    simpa [Set.mem_empty_iff_false] using hB
  exact hFalse.elim

theorem P3_prod_empty {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : P3 (Set.prod A (∅ : Set Y)) := by
  intro p hp
  rcases hp with ⟨_, hY⟩
  cases hY

theorem P2_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} (hA : P2 A) : P2 (e '' A) := by
  intro y hy
  -- 1.  Find a preimage point `x : X` with `x ∈ A`.
  rcases hy with ⟨x, hxA, rfl⟩
  -- 2.  Apply `P2` for `A`.
  have hx_int : x ∈ interior (closure (interior A)) := hA hxA
  -- 3.  Transport the membership with the homeomorphism `e`.
  have h₁ : e x ∈ (⇑e) '' interior (closure (interior A)) :=
    ⟨x, hx_int, rfl⟩
  -- 4.  Use `e.image_interior` to rewrite.
  have h₂ : e x ∈ interior ((⇑e) '' closure (interior A)) := by
    have h_eq := e.image_interior (s := closure (interior A))
    simpa [h_eq] using h₁
  -- 5.  Use `e.image_closure` to push the `closure` through the image.
  have h₃ : e x ∈ interior (closure ((⇑e) '' interior A)) := by
    have h_eq := e.image_closure (s := interior A)
    simpa [h_eq] using h₂
  -- 6.  One more use of `e.image_interior` to obtain the desired set.
  have h₄ : e x ∈ interior (closure (interior ((⇑e) '' A))) := by
    have h_eq := e.image_interior (s := A)
    simpa [h_eq] using h₃
  simpa using h₄

theorem P3_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h_open : IsOpen (closure A)) : P3 A := by
  intro x hxA
  have hx_closure : x ∈ closure A := subset_closure hxA
  simpa [h_open.interior_eq] using hx_closure