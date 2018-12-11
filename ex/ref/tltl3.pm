# User-defined operators

sub happens_before() {
  my ($p,$q) = @_;
  [&and, $p, [&not, &occ($q,[&true])]];
}

# User-defined contexts
[
"thread_init",
&happens_before("spawn","init"),
"other_alive",
[&gt(20), &occ(&any_up("other1","other2","other3"),[&not, "alive"])],
"alive20",
[&gtRT(20), [&not, "alive"]],
"req_ack",
[&gt(5), &occ(&up("req"),[&not, "ack"])],
"alive_done",
&happens_before([&gtRT(20), [&not, "alive"]],"done"),
]
