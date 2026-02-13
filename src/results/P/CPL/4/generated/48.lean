

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