# User-defined operators


# User-defined contexts
[
"tv",
"tv_salon_real_status",
"shower",
[&lt(180000), &between("C21",[&or, "Eau_Froide_Douche_Instantanee", "Eau_Chaude_Douche_Instantanee"])],
"cook",
&occ(&any_up("C3","C14","C15","C16","C17"),[&or, "Intensite_Four", [&or, "Intensite_Hote", "Intensite_Plaques"]]),
"sleep",
[&ge(3600000), "bed_pressure"],
"toilet",
"Eau_Froide_WC_Instantanee",
"dishes",
"Eau_Chaude_Evier_Instantanee",
]
