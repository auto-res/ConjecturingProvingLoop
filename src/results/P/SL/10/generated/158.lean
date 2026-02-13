

theorem Topology.continuous_closure_preimage_subset {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} (hf : Continuous f)
    {B : Set Y} :
    closure (f ⁻¹' B) ⊆ f ⁻¹' closure B := by
  intro x hx
  -- `hx` gives a neighbourhood criterion for `x` with respect to `f ⁻¹' B`.
  have h_closure :
      ∀ V : Set X, IsOpen V → x ∈ V → (V ∩ (f ⁻¹' B)).Nonempty :=
    (mem_closure_iff).1 hx
  -- We will verify the neighbourhood criterion for `f x` and `B`.
  have h_goal :
      ∀ W : Set Y, IsOpen W → f x ∈ W → (W ∩ B).Nonempty := by
    intro W hWopen hfxW
    -- The preimage of `W` is an open neighbourhood of `x`.
    have h_preimage_open : IsOpen (f ⁻¹' W) := hWopen.preimage hf
    have hx_preimage : x ∈ f ⁻¹' W := hfxW
    -- Apply the closure criterion at `x`.
    have h_nonempty :
        ((f ⁻¹' W) ∩ (f ⁻¹' B)).Nonempty :=
      h_closure (f ⁻¹' W) h_preimage_open hx_preimage
    -- Map the witness forward via `f`.
    rcases h_nonempty with ⟨y, hy⟩
    rcases hy with ⟨hyW, hyB⟩
    exact ⟨f y, And.intro hyW hyB⟩
  -- Conclude that `f x` is in the closure of `B`.
  have h_fx : f x ∈ closure B := (mem_closure_iff).2 h_goal
  simpa using h_fx