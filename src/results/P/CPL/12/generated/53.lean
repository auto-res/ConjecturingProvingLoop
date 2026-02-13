

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