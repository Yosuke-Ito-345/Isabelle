# Main Changes from afp-devel as of January 2026

The following are the main changes from afp-devel ba2f4470e120fa0c7e9e4aeb98345ac5d4c1b0cd.

## Newly Added Lemmas

### Preliminaries_AC
- Added `indicator_Ici_right_continuous`, `nn_set_integral_eq_set_integral2`, `set_integrable_iff_bounded`, `LBINT_powr_Icc`, `LBINT_powr_Ici`, `LBINT_powr_Iic`.

### Survival_model

## Incompatible Changes

### Preliminaries_AC
- Renamed the lemma `inverse_powr` to `divide_powr` and dropped the unnecessary assumption.
- Renamed the lemma `powr_at_top` to `powr_at_top_at_top`.
- Slightly changed the lemmas `expectation_nonpos_tail` and `expectation_tail`.

### Survival_model
- Moved the definition `force_mortal` from the locale `smooth_survival_function` to `survival_model`.

### Life_Table
- Moved the notation `force_mortal` from the locale `smooth_life_table` to `life_table`.
