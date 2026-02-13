

theorem inter_subset_closure_left_right {X : Type*} [TopologicalSpace X]
    {U V A B : Set X} (hU : U ⊆ closure A) (hV : V ⊆ closure B) :
    (U ∩ V : Set X) ⊆ closure A ∩ closure B := by
  intro x hx
  exact And.intro (hU hx.1) (hV hx.2)