

theorem closure_inter_closure_compl_eq_frontier {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure A ∩ closure (Aᶜ) = frontier A := by
  -- First, rewrite `closure (Aᶜ)` using a standard complement formula.
  have h : (closure (Aᶜ) : Set X) = (interior A)ᶜ :=
    closure_compl_eq_compl_interior (A := A)
  -- Prove the desired equality by set extensionality.
  ext x
  constructor
  · intro hx
    -- `hx` gives `x ∈ closure A` and `x ∈ closure (Aᶜ)`.
    have hx₁ : x ∈ closure A := hx.1
    have hx₂ : x ∈ (interior A)ᶜ := by
      -- Replace `closure (Aᶜ)` with `(interior A)ᶜ` using `h`.
      simpa [h] using hx.2
    -- Combine the two facts to obtain membership in `frontier A`.
    exact And.intro hx₁ hx₂
  · intro hx
    -- `hx` gives `x ∈ closure A` and `x ∈ (interior A)ᶜ`.
    have hx₁ : x ∈ closure A := hx.1
    have hx₂ : x ∈ closure (Aᶜ) := by
      -- Replace `(interior A)ᶜ` with `closure (Aᶜ)` using `h`.
      simpa [h] using hx.2
    -- Combine the two facts to obtain membership in the intersection.
    exact And.intro hx₁ hx₂