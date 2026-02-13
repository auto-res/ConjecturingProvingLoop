

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