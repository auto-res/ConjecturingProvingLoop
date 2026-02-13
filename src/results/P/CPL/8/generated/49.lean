

theorem P2_prod_inf {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A₁ A₂ : Set X} {B₁ B₂ : Set Y} : P2 A₁ → P2 A₂ → P2 B₁ → P2 B₂ → P2 (Set.prod (A₁ ∩ A₂) (B₁ ∪ B₂)) := by
  intro hP2A₁ hP2A₂ hP2B₁ hP2B₂
  -- `P2` for the intersection of `A₁` and `A₂`
  have hA : P2 (A₁ ∩ A₂) := P2_inter (A := A₁) (B := A₂) hP2A₁ hP2A₂
  -- `P2` for the union of `B₁` and `B₂`
  have hB : P2 (B₁ ∪ B₂) := P2_union (A := B₁) (B := B₂) hP2B₁ hP2B₂
  -- Combine via the product lemma
  exact P2_prod (A := A₁ ∩ A₂) (B := B₁ ∪ B₂) hA hB

theorem P3_interior_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P3 (interior A) → P3 (interior B) → P3 (interior (A ∪ B)) := by
  intro _ _
  exact P3_of_open (A := interior (A ∪ B)) isOpen_interior

theorem P2_compl_compl {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A ↔ P2 (Aᶜᶜ) := by
  simpa [compl_compl] using (Iff.rfl : P2 A ↔ P2 A)

theorem P1_of_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : P1 A := by
  intro x hxA
  -- Any nonempty subset of a subsingleton type is the whole space.
  have hAuniv : (A : Set X) = Set.univ := by
    ext y
    constructor
    · intro _; exact Set.mem_univ y
    · intro _
      have : y = x := Subsingleton.elim _ _
      simpa [this] using hxA
  -- The desired claim follows after rewriting with `hAuniv`.
  simpa [hAuniv, interior_univ, closure_univ] using (Set.mem_univ x)