

theorem closureInterior_prod_subset_closureInterior_prod
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} :
    closure (interior A) ×ˢ closure (interior B) ⊆
      closure (interior (A ×ˢ B)) := by
  intro z hz
  have h_eq :
      closure (interior (A ×ˢ B)) =
        closure (interior A) ×ˢ closure (interior B) :=
    closure_interior_prod (X := X) (Y := Y) (A := A) (B := B)
  simpa [h_eq] using hz