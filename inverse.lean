import .util

namespace inverse
    open function
    open classical (renaming some → unexists) (renaming some_spec → unexists_prop)
    open classical (choice prop_decidable)
    local attribute [instance] prop_decidable

    open util

    -- one-sided inverses:
    class invertible.one_sided {T T': Sort _} (f: T → T') :=
        (g: T' → T)
        (left_inv:
            ∀ x: T,
            g (f x) = x)

    @[reducible, inline] def inv {T T': Sort _} (f: T → T') [hf: invertible.one_sided f]:
        T' → T := hf.g

    @[simp] theorem inv.elim {T T': Sort _} (f: T → T') [hf: invertible.one_sided f]:
        ∀ x: T,
        inv f (f x) = x := by apply hf.left_inv

    instance inv.surjective {T T': Sort _} (f: T → T') [hf: invertible.one_sided f]:
        surjective (inv f) := begin
            intro x,
            apply exists.intro (f x),
            simp,
        end

    instance invertible.one_sided.injective {T T': Sort _} (f: T → T') [hf: invertible.one_sided f]:
        injective f := begin
            intros x y hxy,
            have hinvxy: inv f (f x) = inv f (f y) := congr rfl hxy,
            simp at hinvxy,
            assumption,
        end


    -- noncomputable inverse:
    noncomputable def inj_inv {T T': Sort _} [hT: nonempty T] (f: T → T') (y: T'): T :=
        if h: ∃ x: T, f x = y then
            unexists h
        else
            choice hT

    noncomputable def inj_inv.is_inverse {T T': Sort _} [hT: nonempty T] (f: T → T') [hf: injective f]:
        invertible.one_sided f := {
            g := inj_inv f,
            left_inv := begin
                intros,
                rw [inj_inv],
                cases em (∃ (x' : T), f x' = f x),
                case or.inl {
                    rw [dif_pos h],
                    apply hf,
                    exact unexists_prop h,
                },
                case or.inr {
                    rw [dif_neg h],
                    apply false.elim,
                    apply h,
                    apply exists.intro x,
                    refl,
                },
            end,
        }


    -- two-sided inverses:
    class invertible {T T': Sort _} (f: T → T') extends invertible.one_sided f :=
        (right_inv:
            ∀ y: T',
            f (g y) = y)

    instance invertible.surjective {T T': Sort _} (f: T → T') [hf: invertible f]:
        surjective f := begin
            intro y,
            apply exists.intro ((inv f) y),
            rw [hf.right_inv],
        end

    instance invertible.bijective {T T': Sort _} (f: T → T') [hf: invertible f]:
        bijective f := {
            -- injective:
            left := by apply invertible.one_sided.injective,
            -- surjective:
            right := by apply invertible.surjective,
        }

    instance invertible.of_surjective {T T': Sort _} (f: T → T') [hfinv: invertible.one_sided f] [hfsur: surjective f]:
        invertible f := begin
            split,
            intros,
            have hex := hfsur y,
            apply exists.elim hex,
            intros x hx,
            rw [←hx],
            exact congr rfl (invertible.one_sided.left_inv f x),
        end

    instance inv.invertible {T T': Sort _} (f: T → T') [hf: invertible f]:
        invertible (inv f) := {
            g := f,
            left_inv := hf.right_inv,
            right_inv := hf.left_inv,
        }

    @[simp] theorem inv.elim_of_inv {T T': Sort _} (f: T → T') [hf: invertible f]:
        inv (inv f) = f := by rw [inv.invertible]

    theorem inv.uniq {T T': Sort _} (f: T → T') [hf: invertible f]:
        ∀ {g: T' → T},
        (∀ x: T, g (f x) = x) →
        g = inv f := begin
            intros g hg,
            funext,
            have hfsurx := invertible.surjective f x,
            apply exists.elim hfsurx,
            intros y hy,
            rw [←hy, hg y],
            rw [inv, hf.left_inv],
        end

    instance inv.injective {T T': Sort _} (f: T → T') [hf: invertible f]:
        injective (inv f) := begin
            intros x y hxy,
            have hfx := invertible.surjective f x,
            have hfy := invertible.surjective f y,
            apply exists.elim hfx,
            intros a ha,
            apply exists.elim hfy,
            intros b hb,
            rw [←ha, ←hb] at *,
            simp at hxy,
            rw [hxy],
        end


    -- id:
    instance id.invertible {T: Sort _}:
        invertible (@id T) := {
            g := id,
            left_inv := begin
                intros,
                refl,
            end,
            right_inv := begin
                intros,
                refl,
            end,
        }
end inverse
