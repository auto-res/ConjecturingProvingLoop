

theorem interior_closure_union_satisfies_P3
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 (interior (closure (A : Set X)) ∪ interior (closure B)) := by
  -- `interior (closure A)` and `interior (closure B)` are both open.
  have hOpenA : IsOpen (interior (closure (A : Set X))) := isOpen_interior
  have hOpenB : IsOpen (interior (closure (B : Set X))) := isOpen_interior
  -- Their union is therefore open.
  have hOpen : IsOpen (interior (closure (A : Set X)) ∪ interior (closure B)) :=
    hOpenA.union hOpenB
  -- Any open set satisfies `P3`.
  exact Topology.open_satisfies_P3
    (A := interior (closure (A : Set X)) ∪ interior (closure B)) hOpen