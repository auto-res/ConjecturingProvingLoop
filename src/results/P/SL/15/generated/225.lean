

theorem closure_prod_eq_closure_interior_prod_of_P1
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y}
    (hA : Topology.P1 A) (hB : Topology.P1 B) :
    closure (A ×ˢ B) = closure (interior A) ×ˢ closure (interior B) := by
  -- Express `closure A` and `closure B` via the `P1` property.
  have hA_cl : closure (A : Set X) = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)).1 hA
  have hB_cl : closure (B : Set Y) = closure (interior B) :=
    (Topology.P1_iff_closure_eq_closure_interior (X := Y) (A := B)).1 hB
  -- Rewrite the closure of the product using these equalities.
  calc
    closure (A ×ˢ B) =
        closure (A : Set X) ×ˢ closure (B : Set Y) := by
          simpa using closure_prod_eq (s := A) (t := B)
    _ = closure (interior A) ×ˢ closure (interior B) := by
          simpa [hA_cl, hB_cl]