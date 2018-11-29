# User-defined operators


# User-defined contexts
[
"c1a",
[&or, [&not, "Hb"], &met("Hb","Gb")],
"c1b",
[&or, [&not, "Gb"], &met("Gb","Nhb")],
"c1c",
[&or, [&not, "Gb"], [&and, &during("Gb","H"), &during("Gb","At(tree)")]],
"c2a",
[&or, [&not, "At(tree)"], &met("At(tree)","G(x,tree)")],
"c2b",
[&or, [&not, "G(x,tree)"], &met("G(x,tree)","At(x)")],
"c2c",
[&or, [&not, "G(x,tree)"], &during("G(x,tree)","L")],
"c3a",
[&or, [&not, "H"], &met("H","C")],
"c3b",
[&or, [&not, "C"], &met("C","L")],
"c3c",
[&or, [&not, "CD"], &met("CD","H")],
"c3d",
[&or, [&not, "C"], &during("C","At(tree)")],
"c4a",
[&or, [&not, "Gb"], &during("Gb","hungry")],
"c4b",
[&or, [&not, "Hb"], &during("Hb","hungry")],
"c5a",
[&or, [&not, "Nhb"], &ex("hungry","Nhb")],
"c5b",
[&or, [&not, "Gb"], &holds("hungry","Gb")],
]
