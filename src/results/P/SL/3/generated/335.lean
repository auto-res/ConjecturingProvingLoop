

theorem closure_inter_interior_subset_inter_closures {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure ((A ∩ interior (B : Set X)) : Set X) ⊆
      closure (A : Set X) ∩ closure (B : Set X) := by
  -- We start with the inclusion into `closure A ∩ closure (interior B)`
  have h₁ :
      closure ((A ∩ interior (B : Set X)) : Set X) ⊆
        closure (A : Set X) ∩ closure (interior (B : Set X)) :=
    closure_inter_interior_subset_closure_interiors (A := A) (B := B)
  -- Since `interior B ⊆ B`, taking closures yields
  -- `closure (interior B) ⊆ closure B`.
  have h₂ : closure (interior (B : Set X)) ⊆ closure (B : Set X) :=
    closure_mono (interior_subset (s := B))
  -- Combine the two inclusions to obtain the desired result.
  intro x hx
  have hx' : (x : X) ∈ closure (A : Set X) ∩ closure (interior (B : Set X)) := h₁ hx
  exact And.intro hx'.1 (h₂ hx'.2)