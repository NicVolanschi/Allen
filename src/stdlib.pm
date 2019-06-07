# Copyright 2018,2019 Inria. This file is part of Allen.
#
# Allen is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# Allen is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with Allen.  If not, see <https://www.gnu.org/licenses/>.

#
# Standard library for the Allen language.
# Contains default implementations for commonly used operators.
#

# ------------------------------------------------------
# Operators adapted from Allen logic

sub meets() {
  my ($p, $q) = @_;
  return [\&meets2, $p, $q];
}

sub met() {
  my ($p, $q) = @_;
  return [\&met2, $p, $q];
}

sub starts() {
  my ($p, $q) = @_;
  return [\&starts2, $p, $q];
}

sub ends() {
  my ($p, $q) = @_;
  return [\&ends2, $p, $q];
}

sub started() {
  my ($p, $q) = @_;
  return &occ(&starts($q, $p), $p);
}

sub ended() {
  my ($p, $q) = @_;
  return &ex(&ends($q, $p), $p);
}

sub eq() {
  my ($p, $q) = @_;
  return [\&eq2, $p, $q];
}

sub during() {
  my ($p, $q) = @_;
  return [\&during2, $p, $q];
}

sub contains() {
  my ($p, $q) = @_;
  return &ex(&during( $q, $p), $p);
}

sub over() {
  my ($p, $q) = @_;
  return [\&over2, $p, $q];
}

sub overlaps() {
  my ($p, $q) = @_;
  return &ex(&over($p, $q), $p);
}

sub overlapped() {
  my ($p, $q) = @_;
  return &occ(&over($q, $p), $p);
}

sub holds() {
  my ($p, $q) = @_;
  return [\&holds2, $p, $q];
}

# exists(p,q)
sub ex() {
  my ($p, $q) = @_;
  return [&and, $q, [&not, &holds( [&not, $p], $q)]];
}

sub occ() {
  my ($p, $q) = @_;
  return [\&occ2, $p, $q];
}

sub btw() {
  my ($p, $q) = @_;
  return &over([&not, $q], [&not, $p]);
}

sub between() {
  my ($p, $q) = @_;
  return [\&between2, $p, $q];
}

sub before() {
  my ($p, $q) = @_;
  return &meets($p, &between($p, $q));
}

sub after() {
  my ($p, $q) = @_;
  return &met($p, &between($q, $p));
}

sub btwin() {
  my ($p, $q) = @_;
  return [\&btwin2, $p, $q];
}

# True if p=>valp comes before q=>valq
sub left() {
  my ($ref_p, $ref_q, $t, $valp, $valq) = @_;
  my $tpv = &next_val($t, $ref_p, $valp);
  my $tqv = &next_val($t, $ref_q, $valq);
  return defined($tpv) &&
          defined(&val($ref_q, $tpv)) &&
          (!defined($tqv) || $tpv < $tqv);
          # q constant until after p changes
}

# True if p=>valp comes before or when q=>valq
sub lefteq() {
  my ($ref_p, $ref_q, $t, $valp, $valq) = @_;
  my $tpv = &next_val($t, $ref_p, $valp);
  my $tqv = &next_val($t, $ref_q, $valq);
  return defined($tpv) &&
          (defined(&val($ref_q, $tpv)) || &tsval($ref_q, $tpv)->[0] == $tpv) &&
          (!defined($tqv) || $tpv <= $tqv);
          # q constant until p changes (q may change or become ? at same time)
}

# True if p=>valp comes after q=>valq
sub right() {
  my ($ref_p, $ref_q, $t, $valp, $valq) = @_;
  return &left($ref_q, $ref_p, $t, $valq, $valp);
}

# True if p=>valp comes after or when q=>valq
sub righteq() {
  my ($ref_p, $ref_q, $t, $valp, $valq) = @_;
  return &lefteq($ref_q, $ref_p, $t, $valq, $valp);
}

# True if p=>valp comes exactly when q=>valq
sub sync() {
  my ($ref_p, $ref_q, $t, $valp, $valq) = @_;
  my $tpv = &next_val($t, $ref_p, $valp);
  my $tqv = &next_val($t, $ref_q, $valq);
  return defined($tpv) && defined($tqv) && $tpv == $tqv;
}

sub holds_lookahead() {
  my ($t, $ref_p, $ref_q) = @_;
  if(&righteq($ref_p, $ref_q, $t, 0, 0)) {
  # p=1 until q=>0 (may fall or become ? at same time)
    return 1;
  } elsif(&left($ref_p, $ref_q, $t, 0, 0)) {
    # q=1 until after p=>0 (may NOT fall at same time)
    return 0;
  } else {
    return undef;
  }
}

sub holds2() {
  my ($t, $ref_p, $ref_q, $ref_res, $resval) = @_;
  my $p = &tsval($ref_p, $t);
  my $q = &tsval($ref_q, $t);
  my $valp = $p->[1];
  my $valq = $q->[1];
  #print STDERR "tsval(p,$t)=[$p->[0],$valp], val(q,$t)=[$q->[0],$valq]\n";
  if($t == 0) {
    if (defined($valp) && $valp == 0 || defined($valq) && $valq == 0) {
      return 0;
    } elsif (defined($valp) && $valp == 1 && defined($valq) && $valq == 1) {
      return &holds_lookahead($t, $ref_p, $ref_q);
    } else {
      return undef;
    }
  }
  if($p->[0] == $t && $q->[0] < $t ||
     $p->[0] == $t && $q->[0] == $t && &sameval($valq, &lastval($ref_q, $t))) {
    # only p
    if(&sameval($valp, &lastval($ref_p, $t))) { return $resval; } # nothing
    else {
      if(defined($valp) && $valp == 1) {# p=>1
        die "assert(holds=0) as p was 0" if $resval;
        if(defined($valq)) {# p=>1 & q=0/1
          return 0; # holds stays 0
        } else {# p=>1 & q=?
          return undef;
          # in fact holds=0 at t, but may not last until next()
        }
      } elsif(defined($valp) && $valp == 0) {# p=>0 & q=0/1/?
        die "assert(holds=0) as it would have been reset at q=>0" if $resval;
        die "assert(q=def) as if p was 1 & q was ?, then holds=?"
          if !defined($valp);
        #if(defined($valq)) {
        return 0; # holds stays 0
        #}
      } else {# p=>?
        die "assert(holds=0) as if 1, you'd know p until it gets 0"
          if $resval;
        if(defined($valq) && $valq == 0) {# p=>? & q=0
          return 0; # holds stays 0
        } elsif(defined($valq) && $valq == 1) {# p=>? & q=1
          return 0; # holds stays 0; you're in a void q=1 interval
        } else {# p=>? & q=?
          die "assert(p was 0) as holds=0" if &lastval($ref_p, $t);
          return undef;
        }
      }
    }
  } elsif($p->[0] < $t && $q->[0] == $t ||
          $p->[0] == $t && $q->[0] == $t && &sameval($valp, &lastval($ref_p, $t))) {
    # only q
    if(&sameval($valq, &lastval($ref_q, $t))) { return $resval; } # nothing
    else {
      if(defined($valq) && $valq == 1) {# q=>1
        die "assert(holds=0) as q was 0" if $resval;
        if(defined($valp) && $valp == 0) {# q=>1 & p=0
          return 0; # holds stays 0
        } elsif(defined($valp) && $valp == 1) {# q=>1 & p=1
	        return &holds_lookahead($t, $ref_p, $ref_q);
        } else {# q=>1 & p=?
          return undef;
        }
      } elsif(defined($valq) && $valq == 0) {# q=>0 & p=0/1/?
        if($resval == 1) {
          return 0; # end of a filled q interval
        } else { return 0; } # holds stays 0
      } else {# q=>?
        if(defined($valp) && $valp == 0) {# q=>? & p=0
          die "assert(holds=0) as p=0" if $resval;
          return 0; # holds stays 0
        } elsif(defined($valp) && $valp == 1) {# q=>? & p=1
          return undef;
        } else {# q=>? & p=?
          return undef;
        }
      }
    }
  } elsif($p->[0] == $t && $q->[0] == $t) { # p & q
    # cases when p xor q didn't change were handled as singleton events
    # so check here only the case when none changed:
    if(&sameval($valp, &lastval($ref_p, $t)) &&
       &sameval($valq, &lastval($ref_q, $t))) { return $resval; } # nothing
    else {
      if(defined($valp) && $valp == 0 && defined($valq) && $valq == 0) {
        # p=>0 & q=>0
        if($resval == 1) {
          return 0;
        } else { return 0; } # holds stays 0
      } elsif(defined($valp) && $valp == 0 && defined($valq) && $valq == 1) {
        # p=>0 & q=>1
        die "assert(holds=0) as q was 0" if $resval;
        return 0; # hold stays 0
      } elsif(defined($valp) && $valp == 1 && defined($valq) && $valq == 0) {
        # p=>1 & q=>0
        die "assert(holds=0) as p was 0" if $resval;
        return 0; # holds stays 0
      } elsif(defined($valp) && $valp == 1 && defined($valq) && $valq == 1) {
        # p=>1 & q=>1
        # idem p=1 & q=>1:
	      return &holds_lookahead($t, $ref_p, $ref_q);
      } elsif(defined($valp) && $valp == 0 && !defined($valq)) {
        # p=>0 & q=>?
        die "assert(holds=0) as otherwise you'd know that q=>0 before/when p=>0"
          if $resval;
        return 0; # holds stays 0
      } elsif(defined($valp) && $valp == 1 && !defined($valq)) {
        # p=>1 & q=>?
        die "assert(holds=0) as p was 0" if $resval;
        return undef;
        # NB: even in cases when you could tell that holds is 0, e.g. when
        # q was 1, this value may not last until next()
      } elsif(!defined($valp) && defined($valq) && $valq == 0) {
        # p=>? & q=>0
        if($resval) {
          return 0;
        } else { return 0; } # holds stays 0
      } elsif(!defined($valp) && defined($valq) && $valq == 1) {
        # p=>? & q=>1
        return undef;
      } else {
        # p=>? & q=>?
        return undef;
      }
    }
  }
  die "holds2: void return";
}

sub occ2_init() {
  my ($ref_p, $ref_q) = @_;
  #die "initial value of p undefined" if $#$ref_p < 0;
  #die "initial value of q undefined" if $#$ref_q < 0;
  #return $$ref_p[0][1] && $$ref_q[0][1];
  return &and2_pointwise(&val($ref_p, 0), &val($ref_q, 0));
}

sub occ2() {
  my ($t, $ref_p, $ref_q, $ref_res, $resval) = @_;
  if($t == 0) { return &occ2_init($ref_p, $ref_q); }
  my $p = &tsval($ref_p, $t);
  my $q = &tsval($ref_q, $t);
  my $valp = $p->[1];
  my $valq = $q->[1];
  #print STDERR "tsval(p,$t)=[$p->[0],$valp], val(q,$t)=[$q->[0],$valq]\n";
  if($p->[0] == $t && $q->[0] < $t ||
     $p->[0] == $t && $q->[0] == $t && &sameval($valq, &lastval($ref_q, $t))) {
    # only p
    if(&sameval($valp, &lastval($ref_p, $t))) { return $resval; } # nothing
    else {
      if(defined($valp) && $valp == 1) {# p=>1
        if(defined($valq) && $valq == 0) {# p=>1 & q=0
          die "assert(occ=0) as q was 0" if $resval;
          return 0; # stay 0
        } elsif(defined($valq) && $valq == 1) {# p=>1 & q=1
            return 1; # become or stay 1
        } else {# p=>1 & q=?
          return undef;
        }
      } elsif(defined($valp) && $valp == 0) {# p=>0 & q=0/1/?
        if(defined($valq) && $valq == 0) {# p=>0 & q=0
          die "assert(occ=0) as q was 0" if $resval;
          return 0;
        } elsif(defined($valq) && $valq == 1) {# p=>0 & q=1
          die "assert(occ=1) as p was 1" if defined($resval) && $resval == 0;
          return 1; # stay 1
        } else {# p=>0 & q=?
          die "assert(occ=?) as p was 1" if defined($resval);
          return undef; # stay undef
        }
      } else {# p=>?
        if(defined($valq) && $valq == 0) {# p=>? & q=0
          die "assert(occ=0) as q was 0" if $resval;
          return 0; # stay 0
        } elsif(defined($valq) && $valq == 1) {# p=>? & q=1
          if($resval == 1) {
            return 1; # stay 1, p doesn't matter anymore
          } else {
            return undef;
          }
        } else {# p=>? & q=?
          die "can this happen??" if $resval;
          return undef;
        }
      }
    }
  } elsif($p->[0] < $t && $q->[0] == $t ||
          $p->[0] == $t && $q->[0] == $t && &sameval($valp, &lastval($ref_p, $t))) {
    # only q
    if(&sameval($valq, &lastval($ref_q, $t))) { return $resval; } # nothing
    else {
      if(defined($valq) && $valq == 1) {# q=>1
        die "assert(occ=0) as q was 0" if $resval;
        if(defined($valp) && $valp == 0) {# q=>1 & p=0
          return 0; # stay 0
        } elsif(defined($valp) && $valp == 1) {# q=>1 & p=1
          return 1;
        } else {# q=>1 & p=?
          return undef;
        }
      } elsif(defined($valq) && $valq == 0) {# q=>0 & p=0/1/?
        return 0; # stay or become 0
      } else {# q=>?
        if(defined($valp)) {# q=>? & p=0/1
          return undef;
        } else {# q=>? & p=?
          # q could have been 1/0, and occ too
          return undef;
        }
      }
    }
  } elsif($p->[0] == $t && $q->[0] == $t) { # p & q
    # cases when p xor q didn't change were handled as singleton events
    # so check here only the case when none changed:
    if(&sameval($valp, &lastval($ref_p, $t)) &&
       &sameval($valq, &lastval($ref_q, $t))) { return $resval; } # nothing
    else {
      if(defined($valp) && $valp == 0 && defined($valq) && $valq == 0) {
        # p=>0 & q=>0
        die "assert(occ=1) as p and q were 1"
          if defined($resval) && $resval == 0;
        return 0; # become 0
      } elsif(defined($valp) && $valp == 0 && defined($valq) && $valq == 1) {
        # p=>0 & q=>1
        die "assert(occ=0) as q was 0" if $resval;
        return 0; # stay 0
      } elsif(defined($valp) && $valp == 1 && defined($valq) && $valq == 0) {
        # p=>1 & q=>0
        return 0; # stay or become 0
      } elsif(defined($valp) && $valp == 1 && defined($valq) && $valq == 1) {
        # p=>1 & q=>1
        die "assert(occ=0) as q was 0" if $resval;
        return 1; # become 1
      } elsif(defined($valp) && $valp == 0 && !defined($valq)) {
        # p=>0 & q=>?
        return undef;
        # NB: even in cases when you could tell that occ is 0, e.g. when
        # q was 0, this value may not last until next()
      } elsif(defined($valp) && $valp == 1 && !defined($valq)) {
        # p=>1 & q=>?
        return undef;
      } elsif(!defined($valp) && defined($valq) && $valq == 0) {
        # p=>? & q=>0
        return 0; # stay or become 0
      } elsif(!defined($valp) && defined($valq) && $valq == 1) {
        # p=>? & q=>1
        die "assert(occ=0) as q was 0" if $resval;
        return undef;
      } else {
        # p=>? & q=>?
        return undef;
      }
    }
  }
  die "occ2: void return";
}

sub during_lookahead() {
  my ($t, $ref_p, $ref_q) = @_;
  if(&left($ref_p, $ref_q, $t, 0, 0)) {
    # q=1 until after p=>0 (may NOT fall at same time)
    return 1;
  } elsif(&righteq($ref_p, $ref_q, $t, 0, 0)) {
    # p=1 until q=>0 (may fall or become ? at same time)
    return 0;
  } else {
    return undef;
  }
}

sub during2() {
  my ($t, $ref_p, $ref_q, $ref_res, $resval) = @_;
  if($t == 0) { return 0; }
  my $p = &tsval($ref_p, $t);
  my $q = &tsval($ref_q, $t);
  my $valp = $p->[1];
  my $valq = $q->[1];
  #print STDERR "tsval(p,$t)=[$p->[0],$valp], val(q,$t)=[$q->[0],$valq]\n";
  if($p->[0] == $t && $q->[0] < $t ||
     $p->[0] == $t && $q->[0] == $t && &sameval($valq, &lastval($ref_q, $t))) {
    # only p
    if(&sameval($valp, &lastval($ref_p, $t))) { return $resval; } # nothing
    else {
      if(defined($valp) && $valp == 1) {# p=>1
        die "assert(during=0) as p was 0" if $resval;
        if(defined($valq) && $valq == 0) {# p=>1 & q=0
          return 0; # during stays 0
        } elsif(defined($valq) && $valq == 1) {# p=>1 & q=1
	    return &during_lookahead($t, $ref_p, $ref_q);
        } else {# p=>1 & q=?
          return undef;
        }
      } elsif(defined($valp) && $valp == 0) {# p=>0 & q=0/1/?
        if($resval == 1) {
          return 0; # end of a during interval
        } else { return 0; } # during stays 0
      } else {# p=>?
        die "assert(during=0) as if 1, you'd know p until it gets 0"
          if $resval;
        if(defined($valq) && $valq == 0) {# p=>? & q=0
          return 0; # during stays 0
        } elsif(defined($valq) && $valq == 1) {# p=>? & q=1
          return undef;
          # NB: even in cases when you could tell that during stays 0, e.g. when
          # p was 1, in overlap(p,q), this value may not last until next()
        }
        else {# # p=>? & q=?
          #die "assert(p was 0) as during=0" if &lastval($ref_p, $t);
          #False: p may be 0 or 1 (cf q=>? & p=1 below)
          return undef;
        }
      }
    }
  } elsif($p->[0] < $t && $q->[0] == $t ||
          $p->[0] == $t && $q->[0] == $t && &sameval($valp, &lastval($ref_p, $t))) {
    # only q
    if(&sameval($valq, &lastval($ref_q, $t))) { return $resval; } # nothing
    else {
      if(defined($valq) && $valq == 1) {# q=>1
        die "assert(during=0) as q was 0" if $resval;
        if(defined($valp) && $valp == 0) {# q=>1 & p=0
          return 0; # during stays 0
        } elsif(defined($valp) && $valp == 1) {# q=>1 & p=1
          return 0; # during stays 0
        } else {# q=>1 & p=?
          return undef;
          # in fact during=0 at t, but may not last until next()
        }
      } elsif(defined($valq) && $valq == 0) {# q=>0 & p=0/1/?
        die "assert(during=0) as it would have been reset at p=>0" if $resval;
        die "assert(p=def) as if p was ? & q was 1, then during=?"
          if !defined($valp);
        #if(defined($valp)) {
        return 0; # during stays 0
        #}
      } else {# q=>?
        if(defined($valp) && $valp == 0) {# q=>? & p=0
          die "assert(during=0) as p=0" if $resval;
          return 0; # during stays 0
        } elsif(defined($valp) && $valp == 1) {# q=>? & p=1
          die "assert(during=0) as q=>? would imped it to be 1" if $resval;
          # either lastval(q)=1 (p overlaps q) or lastval(q)=0:
          return 0; # during stays 0
        } else {# q=>? & p=?
          return undef;
        }
      }
    }
  } elsif($p->[0] == $t && $q->[0] == $t) { # p & q
    # cases when p xor q didn't change were handled as singleton events
    # so check here only the case when none changed:
    if(&sameval($valp, &lastval($ref_p, $t)) &&
       &sameval($valq, &lastval($ref_q, $t))) { return $resval; } # nothing
    else {
      if(defined($valp) && $valp == 0 && defined($valq) && $valq == 0) {
        # p=>0 & q=>0
        die "assert(during=0) as anticipated" if $resval;
        return 0; # during stays 0
      } elsif(defined($valp) && $valp == 0 && defined($valq) && $valq == 1) {
        # p=>0 & q=>1
        die "assert(during=0) as qwas 0" if $resval;
        return 0; # hold stays 0
      } elsif(defined($valp) && $valp == 1 && defined($valq) && $valq == 0) {
        # p=>1 & q=>0
        die "assert(during=0) as p was 0" if $resval;
        return 0; # during stays 0
      } elsif(defined($valp) && $valp == 1 && defined($valq) && $valq == 1) {
        # p=>1 & q=>1
        die "assert(during=0) as p and q were 0" if $resval;
        return 0; # during stays 0
      } elsif(defined($valp) && $valp == 0 && !defined($valq)) {
        # p=>0 & q=>?
        die "assert(during=0) as otherwise you'd know that q is 1 after p=>0"
          if $resval;
        return 0; # during stays 0
      } elsif(defined($valp) && $valp == 1 && !defined($valq)) {
        # p=>1 & q=>?
        die "assert(during=0) as p was 0"
          if $resval;
        return undef;
        # NB: even in cases when you could tell that during stays 0, e.g. when
        # q was 1, this value may not last until next()
      } elsif(!defined($valp) && defined($valq) && $valq == 0) {
        # p=>? & q=>0
        die "assert(during=0) as otherwise you'd know that p=>0 before q=>0"
          if $resval;
        return 0; # during stays 0
      } elsif(!defined($valp) && defined($valq) && $valq == 1) {
        # p=>? & q=>1
        return undef;
      } else {
        # p=>? & q=>?
        return undef;
      }
    }
  }
  die "during2: void return";
}

sub btwin_lookahead() {
  my ($t, $ref_p, $ref_q) = @_;
  if(&righteq($ref_p, $ref_q, $t, 1, 1)) {
    return 1;
  } elsif(&left($ref_p, $ref_q, $t, 1, 1)) {
    return 0;
  } else {
    return undef;
  }
}

# true between p=>0 (at t1) and q=>1 (at t2),
# if (t1,t2) nonempty and nothing happens to p and q in it
sub btwin2() {
  my ($t, $ref_p, $ref_q, $ref_res, $resval) = @_;
  if($t == 0) { return 0; }
  my $p = &tsval($ref_p, $t);
  my $q = &tsval($ref_q, $t);
  my $valp = $p->[1];
  my $valq = $q->[1];
  #print STDERR "tsval(p,$t)=[$p->[0],$valp], val(q,$t)=[$q->[0],$valq]\n";
  if($p->[0] == $t && $q->[0] < $t ||
     $p->[0] == $t && $q->[0] == $t && &sameval($valq, &lastval($ref_q, $t))) {
    # only p
    if(&sameval($valp, &lastval($ref_p, $t))) { return $resval; } # nothing
    else {
      if(defined($valp) && $valp == 1) {# p=>1
        die "assert(between=0) as p=>1 was already anticipated" if $resval;
        if(defined($valq)) {# p=>1 & q=0/1
          return 0; # stay 0
        } else {# p=>1 & q=?
          # NB: lastval(q) may be 1, of course, but also 0, in the scenario
          # q=>0; p=>0; q=>?
          return 0; # stay 0
        }
      } elsif(defined($valp) && $valp == 0) {# p=>0 & q=0/1/?
        die "assert(between=0) as p was 1" if $resval;
        if(defined($valq) && $valq == 0) {# p=>0 & q=0
	  return &btwin_lookahead($t, $ref_p, $ref_q);
        } elsif(defined($valq) && $valq == 1) {# p=>0 & q=1
          return 0; # stay 0
        } else {# p=>0 & q=?
          return undef; # become undef
        }
      } else {# p=>?
        if(defined($valq) && $valq == 0) {# p=>? & q=0
          die "assert(between=0) as p=>? would imped it to be 1" if $resval;
          return undef; # become ?
          # NB: even in cases when you could tell that between is 0, e.g. when
          # p was 0, this value may not last until next()
        } elsif(defined($valq) && $valq == 1) {# p=>? & q=1
          die "assert(between=0) as q was 1" if $resval;
          return 0; # stay 0
        } else {# p=>? & q=?
          # NB: lastval(p) may be 1, of course, but also 0, in the scenario
          # q=>0; p=>0; q=>?; p=>?
          return undef;
        }
      }
    }
  } elsif($p->[0] < $t && $q->[0] == $t ||
          $p->[0] == $t && $q->[0] == $t && &sameval($valp, &lastval($ref_p, $t))) {
    # only q
    if(&sameval($valq, &lastval($ref_q, $t))) { return $resval; } # nothing
    else {
      if(defined($valq) && $valq == 1) {# q=>1
        if(defined($valp) && $valp == 0) {# q=>1 & p=0
          return 0; # stay or become 0
        } elsif(defined($valp) && $valp == 1) {# q=>1 & p=1
          die "assert(between=0) as p was 1" if $resval;
          return 0; # stay 0
        } else {# q=>1 & p=?
          die "q=0 & p=? cannot happen, because this would mean between=?";
        }
      } elsif(defined($valq) && $valq == 0) {# q=>0 & p=0/1/?
        die "assert(between=0) as q was 1" if $resval;
        if(defined($valp)) {# q=>0 & p=0/1
          return 0; # stay 0
        } else {# q=>0 & p=?
          return undef;
          # NB: even though you know that between is 0 right now,
          # this value may not last until next()
        }
      } else {# q=>?
        die "assert(between=0) as q=>? would imped it to be 1" if $resval;
        if(defined($valp) && $valp == 1) {# q=>? & p=1
          return 0; # stay 0
        } elsif(defined($valp)) {# q=>? & p=0
          # NB: lastval(q) may be 1, of course, but also 0, in the scenario
          # q=>0; p=>0; q=>?
          return 0; # stay 0
        } else {# q=>? & p=?
          die "assert(q was 1) as q=0 & p=? implies between=?"
            if defined(&lastval($ref_q, $t)) && &lastval($ref_q, $t) == 0;
          return undef;
        }
      }
    }
  } elsif($p->[0] == $t && $q->[0] == $t) { # p & q
    # cases when p xor q didn't change were handled as singleton events
    # so check here only the case when none changed:
    if(&sameval($valp, &lastval($ref_p, $t)) &&
       &sameval($valq, &lastval($ref_q, $t))) { return $resval; } # nothing
    else {
      if(defined($valp) && $valp == 0 && defined($valq) && $valq == 0) {
        # p=>0 & q=>0
        die "assert(between=0) as p and q were 1" if $resval;
	      return &btwin_lookahead($t, $ref_p, $ref_q);
      } elsif(defined($valp) && $valp == 0 && defined($valq) && $valq == 1) {
        # p=>0 & q=>1
        die "assert(between=0) as p was 1" if $resval;
        return 0; # stay 0
        # NB: this case is caught by meets(p,q)
      } elsif(defined($valp) && $valp == 1 && defined($valq) && $valq == 0) {
        # p=>1 & q=>0
        die "assert(between=0) as q was 1" if $resval;
        return 0; # stay 0
      } elsif(defined($valp) && $valp == 1 && defined($valq) && $valq == 1) {
        # p=>1 & q=>1
        return 0; # stay or become o
      } elsif(defined($valp) && $valp == 0 && !defined($valq)) {
        # p=>0 & q=>?
        return undef;
        # NB: even though you know that between is 0 right now,
        # this value may not last until next()
      } elsif(defined($valp) && $valp == 1 && !defined($valq)) {
        # p=>1 & q=>?
        die "assert(between=0) as p=>1 was anticipated if q was 0" if $resval;
        return 0; # stay 0
      } elsif(!defined($valp) && defined($valq) && $valq == 0) {
        # p=>? & q=>0
        die "assert(between=0) as q was 1" if $resval;
        # NB: even though you know that between is 0 right now,
        # this value may not last until next()
        return undef; # become ?
      } elsif(!defined($valp) && defined($valq) && $valq == 1) {
        # p=>? & q=>1
        die "assert(between=0) as p=>? would imped it to be 1" if $resval;
        return 0; # stay 0
      } else {
        # p=>? & q=>?
        return undef;
      }
    }
  }
  die "between2: void return";
}

sub between_lookahead() {
  my ($t, $ref_p, $ref_q) = @_;
  if(&right($ref_p, $ref_q, $t, 0, 1)) {
    return 1;
  } elsif(&lefteq($ref_p, $ref_q, $t, 0, 1)) {
    return 0;
  } else {
    return undef;
  }
}

# true between p=>0 (at t1) and q=>1 (at t2),
# if (t1,t2) nonempty and (t,q) contains no p=>0 or q=>1
# and there is no q=>1 at t1 and no p=>0 at t2
sub between2() {
  my ($t, $ref_p, $ref_q, $ref_res, $resval) = @_;
  if($t == 0) { return 0; }
  my $p = &tsval($ref_p, $t);
  my $q = &tsval($ref_q, $t);
  my $valp = $p->[1];
  my $valq = $q->[1];
  #print STDERR "tsval(p,$t)=[$p->[0],$valp], val(q,$t)=[$q->[0],$valq]\n";
  if($p->[0] == $t && $q->[0] < $t ||
     $p->[0] == $t && $q->[0] == $t && &sameval($valq, &lastval($ref_q, $t))) {
    # only p
    if(&sameval($valp, &lastval($ref_p, $t))) { return $resval; } # nothing
    else {
      if(defined($valp) && $valp == 1) {# p=>1
        if(defined($valq)) {# p=>1 & q=0/1
          return $resval; # no change
        } else {# p=>1 & q=?
          die "assert(between=0) as q=>? would imped it to be 1" if $resval;
          # NB: lastval(q) may be 1, of course, but also 0, in the scenario
          # p=>0; q=>1; q=>0; q=>?
          return 0; # stay 0
        }
      } elsif(defined($valp) && $valp == 0) {# p=>0 & q=0/1/?
        die "assert(between=0) as p=>0 would be anticipated" if $resval;
        if(defined($valq)) {# p=>0 & q=0/1
	  return &between_lookahead($t, $ref_p, $ref_q);
        } else {# p=>0 & q=?
          return undef; # become undef
        }
      } else {# p=>?
        if(defined($valq)) {# p=>? & q=0/1
          die "assert(between=0) as p=>? would imped it to be 1" if $resval;
          return undef; # become ?
        } else {# p=>? & q=?
          return undef;
        }
      }
    }
  } elsif($p->[0] < $t && $q->[0] == $t ||
          $p->[0] == $t && $q->[0] == $t && &sameval($valp, &lastval($ref_p, $t))) {
    # only q
    if(&sameval($valq, &lastval($ref_q, $t))) { return $resval; } # nothing
    else {
      if(defined($valq) && $valq == 1) {# q=>1
        if(defined($valp)) {# q=>1 & p=0/1
          return 0; # stay or become 0
        } else {# q=>1 & p=?
          die "p=? cannot happen, because this would mean between=?";
        }
      } elsif(defined($valq) && $valq == 0) {# q=>0 & p=0/1/?
        if(defined($valp)) {# q=>0 & p=0/1
          # NB: between may be 0 or 1
          return $resval; # no change
        } else {# q=>0 & p=?
          die "p=? cannot happen, because this would mean between=?";
        }
      } else {# q=>?
        die "assert(between=0) as q=>? would imped it to be 1" if $resval;
        if(defined($valp)) {# q=>? & p=0/1
          # NB: this may happen if p didn't fall since q=>1
          return 0; # stay 0
        } else {# q=>? & p=?
          die "p=? cannot happen, because this would mean between=?";
        }
      }
    }
  } elsif($p->[0] == $t && $q->[0] == $t) { # p & q
    # cases when p xor q didn't change were handled as singleton events
    # so check here only the case when none changed:
    if(&sameval($valp, &lastval($ref_p, $t)) &&
       &sameval($valq, &lastval($ref_q, $t))) { return $resval; } # nothing
    else {
      if(defined($valp) && $valp == 0 && defined($valq) && $valq == 0) {
        # p=>0 & q=>0
        die "assert(between=0) as p=>0 would be anticipated" if $resval;
	      return &between_lookahead($t, $ref_p, $ref_q);
      } elsif(defined($valp) && $valp == 0 && defined($valq) && $valq == 1) {
        # p=>0 & q=>1
        die "assert(between=0) as p=>0 would be anticipated" if $resval;
        return 0; # stay 0
        # NB: this case is caught by meets(p,q)
      } elsif(defined($valp) && $valp == 1 && defined($valq) && $valq == 0) {
        # p=>1 & q=>0
        return $resval; # no change
      } elsif(defined($valp) && $valp == 1 && defined($valq) && $valq == 1) {
        # p=>1 & q=>1
        return 0; # stay or become o
      } elsif(defined($valp) && $valp == 0 && !defined($valq)) {
        # p=>0 & q=>?
        die "assert(between=0) as q=>? would imped it to be 1" if $resval;
        return undef;
      } elsif(defined($valp) && $valp == 1 && !defined($valq)) {
        # p=>1 & q=>?
        die "assert(between=0) as q=>? would imped it to be 1" if $resval;
        return 0; # stay 0
      } elsif(!defined($valp) && defined($valq) && $valq == 0) {
        # p=>? & q=>0
        die "assert(between=0) as p=>? would imped it to be 1" if $resval;
        return undef;
      } elsif(!defined($valp) && defined($valq) && $valq == 1) {
        # p=>? & q=>1
        die "assert(between=0) as p=>? would imped it to be 1" if $resval;
        return undef;
      } else {
        # p=>? & q=>?
        return undef;
      }
    }
  }
  die "between2: void return";
}

sub over_lookahead() {
  my ($t, $ref_p, $ref_q) = @_;
  if(&left($ref_p, $ref_q, $t, 0, 0)) {
    return 1;
  } elsif(&righteq($ref_p, $ref_q, $t, 0, 0)) {
    return 0;
  } else {
    return undef;
  }
}

# true during the overlapping of p with q (when both are true)
sub over2() {
  my ($t, $ref_p, $ref_q, $ref_res, $resval) = @_;
  if($t == 0) { return 0; }
  my $p = &tsval($ref_p, $t);
  my $q = &tsval($ref_q, $t);
  my $valp = $p->[1];
  my $valq = $q->[1];
  #print STDERR "tsval(p,$t)=[$p->[0],$valp], val(q,$t)=[$q->[0],$valq]\n";
  if($p->[0] == $t && $q->[0] < $t ||
     $p->[0] == $t && $q->[0] == $t && &sameval($valq, &lastval($ref_q, $t))) {
    # only p
    if(&sameval($valp, &lastval($ref_p, $t))) { return $resval; } # nothing
    else {
      if(defined($valp) && $valp == 1) {# p=>1
        die "assert(over=0) as p was 0" if $resval;
        if(defined($valq)) {# p=>1 & q=0/1
          return 0; # stay 0
        } else {# p=>1 & q=?
          return undef;
          # NB: even though you know that between is 0 right now,
          # this value may not last until next()
        }
      } elsif(defined($valp) && $valp == 0) {# p=>0 & q=0/1/?
        if(defined($valq)) {# p=>0 & q=0/1
          return 0; # stay or become 0
        } else {# p=>0 & q=?
          die "assert(over=0) as q=>? would imped it to be 1" if $resval;
          return 0; # stay 0
        }
      } else {# p=>?
        die "assert(over=0) as p=>? would imped it to be 1" if $resval;
        if(defined($valq) && $valq == 1) {# p=>? & q=1
          return 0; # stay 0
        } elsif(defined($valq)) {# p=>? & q=0
          return 0; # stay 0
        } else {# p=>? & q=?
          return undef;
        }
      }
    }
  } elsif($p->[0] < $t && $q->[0] == $t ||
          $p->[0] == $t && $q->[0] == $t && &sameval($valp, &lastval($ref_p, $t))) {
    # only q
    if(&sameval($valq, &lastval($ref_q, $t))) { return $resval; } # nothing
    else {
      if(defined($valq) && $valq == 1) {# q=>1
        die "assert(over=0) as q was 0" if $resval;
        if(defined($valp) && $valp == 1) {# q=>1 & p=1
	  return &over_lookahead($t, $ref_p, $ref_q);
        } elsif(defined($valp)) {# q=>1 & p=0
          return 0; # stay 0
        } else {# q=>1 & p=?
          return undef;
        }
      } elsif(defined($valq) && $valq == 0) {# q=>0 & p=0/1/?
        if(defined($valp) && $valp == 1) {# q=>0 & p=1
          die "assert(between=0) as p=>0 would be anticipated" if $resval;
          return 0; # stay 0
        } elsif(defined($valp)) {# q=>0 & p=0
          die "assert(over=0) as p was 0" if $resval;
          return 0; # stay 0
        } else {# q=>0 & p=?
          die "assert(over=0) as q=>? would imped it to be 1" if $resval;
          return 0; # stay 0
        }
      } else {# q=>?
        die "assert(over=0) as q=>? would imped it to be 1" if $resval;
        if(defined($valp) && $valp == 1) {# q=>? & p=1
          return undef;
        } elsif(defined($valp)) {# q=>? & p=0
          return 0; # stay 0
        } else {# q=>? & p=?
          return undef;
        }
      }
    }
  } elsif($p->[0] == $t && $q->[0] == $t) { # p & q
    # cases when p xor q didn't change were handled as singleton events
    # so check here only the case when none changed:
    if(&sameval($valp, &lastval($ref_p, $t)) &&
       &sameval($valq, &lastval($ref_q, $t))) { return $resval; } # nothing
    else {
      if(defined($valp) && $valp == 0 && defined($valq) && $valq == 0) {
        # p=>0 & q=>0
        die "assert(over=0) as p=>0 would be anticipated" if $resval;
          return 0;
      } elsif(defined($valp) && $valp == 0 && defined($valq) && $valq == 1) {
        # p=>0 & q=>1
        die "assert(over=0) as q was 0" if $resval;
        return 0; # stay 0
      } elsif(defined($valp) && $valp == 1 && defined($valq) && $valq == 0) {
        # p=>1 & q=>0
        die "assert(over=0) as p was 0" if $resval;
        return 0; # stay 0
      } elsif(defined($valp) && $valp == 1 && defined($valq) && $valq == 1) {
        # p=>1 & q=>1
        die "assert(over=0) as p was 0" if $resval;
        return 0; # stay 0
      } elsif(defined($valp) && $valp == 0 && !defined($valq)) {
        # p=>0 & q=>?
        die "assert(over=0) as q=>? would imped it to be 1" if $resval;
        return 0;
      } elsif(defined($valp) && $valp == 1 && !defined($valq)) {
        # p=>1 & q=>?
        die "assert(over=0) as p was 0" if $resval;
        return undef;
        # NB: even though you know that between is 0 right now,
        # this value may not last until next()
      } elsif(!defined($valp) && defined($valq) && $valq == 0) {
        # p=>? & q=>0
        die "assert(over=0) as p=>? would imped it to be 1" if $resval;
        return 0;
      } elsif(!defined($valp) && defined($valq) && $valq == 1) {
        # p=>? & q=>1
        die "assert(over=0) as q was 0" if $resval;
        if(&lastval($ref_p, $t) == 1) {
          return undef;
        } else { # p was 0
          return 0;
        }
      } else {
        # p=>? & q=>?
        return undef;
      }
    }
  }
  die "over2: void return";
}

sub starts_lookahead() {
  my ($t, $ref_p, $ref_q) = @_;
  if(&left($ref_p, $ref_q, $t, 0, 0)) {
    return 1;
  } elsif(&righteq($ref_p, $ref_q, $t, 0, 0)) {
    return 0;
  } else {
    return undef;
  }
}

# true during the intervals of p which start an interval of q
sub starts2() {
  my ($t, $ref_p, $ref_q, $ref_res, $resval) = @_;
  my $p = &tsval($ref_p, $t);
  my $q = &tsval($ref_q, $t);
  my $valp = $p->[1];
  my $valq = $q->[1];
  #print STDERR "tsval(p,$t)=[$p->[0],$valp], val(q,$t)=[$q->[0],$valq]\n";
  if($t == 0) {
    if (defined($valp) && $valp == 0 || defined($valq) && $valq == 0) {
      return 0;
    } elsif ($valp == 1 && $valq == 1) {
      return &starts_lookahead($t, $ref_p, $ref_q);
    } else {
      return undef;
    }
  }
  if($p->[0] == $t && $q->[0] < $t ||
     $p->[0] == $t && $q->[0] == $t && &sameval($valq, &lastval($ref_q, $t))) {
    # only p
    if(&sameval($valp, &lastval($ref_p, $t))) { return $resval; } # nothing
    else {
      if(defined($valp) && $valp == 1) {# p=>1
        die "assert(starts=0) as p was 0" if $resval;
        if(defined($valq)) {# p=>1 & q=0/1
          return 0; # stay 0
        } else {# p=>1 & q=?
          return undef;
        }
      } elsif(defined($valp) && $valp == 0) {# p=>0 & q=0/1/?
        if(defined($valq)) {# p=>0 & q=0/1
          return 0; # stay or become 0
        } else {# p=>0 & q=?
          die "assert(starts=0) as q=>? would imped it to be 1" if $resval;
          return 0; # stay 0
        }
      } else {# p=>?
        die "assert(starts=0) as p=>? would imped it to be 1" if $resval;
        if(defined($valq) && $valq == 1) {# p=>? & q=1
          return 0; # stay 0
        } elsif(defined($valq)) {# p=>? & q=0
          return 0; # stay 0
        } else {# p=>? & q=?
          return undef;
        }
      }
    }
  } elsif($p->[0] < $t && $q->[0] == $t ||
          $p->[0] == $t && $q->[0] == $t && &sameval($valp, &lastval($ref_p, $t))) {
    # only q
    if(&sameval($valq, &lastval($ref_q, $t))) { return $resval; } # nothing
    else {
      if(defined($valq) && $valq == 1) {# q=>1
        die "assert(starts=0) as q was 0" if $resval;
        if(defined($valp)) {# q=>1 & p=0/1
          return 0; # stay 0
        } else {# q=>1 & p=?
          return undef;
        }
      } elsif(defined($valq) && $valq == 0) {# q=>0 & p=0/1/?
        die "assert(starts=0) as it cannot be 1 until q=>0" if $resval;
        if(defined($valp)) {# q=>0 & p=0/1
          return 0; # stay 0
        } else {# q=>0 & p=?
          return 0; # stay 0
        }
      } else {# q=>?
        die "assert(starts=0) as q=>? would imped it to be 1" if $resval;
        if(defined($valp) && $valp == 1) {# q=>? & p=1
          return 0; # stay 0
        } elsif(defined($valp)) {# q=>? & p=0
          return 0; # stay 0
        } else {# q=>? & p=?
          return undef;
        }
      }
    }
  } elsif($p->[0] == $t && $q->[0] == $t) { # p & q
    # cases when p xor q didn't change were handled as singleton events
    # so check here only the case when none changed:
    if(&sameval($valp, &lastval($ref_p, $t)) &&
       &sameval($valq, &lastval($ref_q, $t))) { return $resval; } # nothing
    else {
      if(defined($valp) && $valp == 0 && defined($valq) && $valq == 0) {
        # p=>0 & q=>0
        die "assert(starts=0) as p=>0 would be anticipated" if $resval;
          return 0;
      } elsif(defined($valp) && $valp == 0 && defined($valq) && $valq == 1) {
        # p=>0 & q=>1
        die "assert(starts=0) as q was 0" if $resval;
        return 0; # stay 0
      } elsif(defined($valp) && $valp == 1 && defined($valq) && $valq == 0) {
        # p=>1 & q=>0
        die "assert(starts=0) as p was 0" if $resval;
        return 0; # stay 0
      } elsif(defined($valp) && $valp == 1 && defined($valq) && $valq == 1) {
        # p=>1 & q=>1
        die "assert(starts=0) as p was 0" if $resval;
	      return &starts_lookahead($t, $ref_p, $ref_q);
      } elsif(defined($valp) && $valp == 0 && !defined($valq)) {
        # p=>0 & q=>?
        die "assert(starts=0) as q=>? would imped it to be 1" if $resval;
        return 0;
      } elsif(defined($valp) && $valp == 1 && !defined($valq)) {
        # p=>1 & q=>?
        die "assert(starts=0) as p was 0" if $resval;
        if(&lastval($ref_q, $t) == 1) {
          return 0;
        } else {
          return undef;
        }
      } elsif(!defined($valp) && defined($valq) && $valq == 0) {
        # p=>? & q=>0
        die "assert(starts=0) as it cannot be 1 until q=>0" if $resval;
        return 0;
      } elsif(!defined($valp) && defined($valq) && $valq == 1) {
        # p=>? & q=>1
        die "assert(starts=0) as q was 0" if $resval;
        if(&lastval($ref_p, $t) == 1) {
          return 0;
        } else { # p was 0
          return undef;
        }
      } else {
        # p=>? & q=>?
        return undef;
      }
    }
  }
  die "starts2: void return";
}

sub eq_lookahead() {
  my ($t, $ref_p, $ref_q) = @_;
  # idem p=>1 & q=>1
  if(&left($ref_p, $ref_q, $t, 0, 0)) {
    return 0;
  } elsif(&right($ref_p, $ref_q, $t, 0, 0)) {
    return 0;
  } elsif(&sync($ref_p, $ref_q, $t, 0, 0)) {
    return 1;
  } else {
      return undef;
  }
}

# true during the intervals of p which equal an interval of q
sub eq2() {
  my ($t, $ref_p, $ref_q, $ref_res, $resval) = @_;
  my $p = &tsval($ref_p, $t);
  my $q = &tsval($ref_q, $t);
  my $valp = $p->[1];
  my $valq = $q->[1];
  #print STDERR "tsval(p,$t)=[$p->[0],$valp], val(q,$t)=[$q->[0],$valq]\n";
  if($t == 0) {
    if (defined($valp) && $valp == 0 || defined($valq) && $valq == 0) {
      return 0;
    } elsif ($valp == 1 && $valq == 1) {
      return &eq_lookahead($t, $ref_p, $ref_q);
    } else {
      return undef;
    }
  }
  if($p->[0] == $t && $q->[0] < $t ||
     $p->[0] == $t && $q->[0] == $t && &sameval($valq, &lastval($ref_q, $t))) {
    # only p
    if(&sameval($valp, &lastval($ref_p, $t))) { return $resval; } # nothing
    else {
      if(defined($valp) && $valp == 1) {# p=>1
        die "assert(eq=0) as p was 0" if $resval;
        if(defined($valq)) {# p=>1 & q=0/1
          return 0; # stay 0
        } else {# p=>1 & q=?
          return undef;
        }
      } elsif(defined($valp) && $valp == 0) {# p=>0 & q=0/1/?
        die "assert(eq=0) as p=>0 would imped it to be 1" if $resval;
        if(defined($valq)) {# p=>0 & q=0/1
          return 0; # stay 0
        } else {# p=>0 & q=?
          die "assert(eq=0) as q=>? would imped it to be 1" if $resval;
          return 0; # stay 0
        }
      } else {# p=>?
        die "assert(eq=0) as p=>? would imped it to be 1" if $resval;
        if(defined($valq) && $valq == 1) {# p=>? & q=1
          return 0; # stay 0
        } elsif(defined($valq)) {# p=>? & q=0
          return 0; # stay 0
        } else {# p=>? & q=?
          return undef;
        }
      }
    }
  } elsif($p->[0] < $t && $q->[0] == $t ||
          $p->[0] == $t && $q->[0] == $t && &sameval($valp, &lastval($ref_p, $t))) {
    # only q
    if(&sameval($valq, &lastval($ref_q, $t))) { return $resval; } # nothing
    else {
      if(defined($valq) && $valq == 1) {# q=>1
        die "assert(eq=0) as q was 0" if $resval;
        if(defined($valp)) {# q=>1 & p=0/1
          return 0; # stay 0
        } else {# q=>1 & p=?
          return undef;
        }
      } elsif(defined($valq) && $valq == 0) {# q=>0 & p=0/1/?
        die "assert(eq=0) as it cannot be 1 until q=>0" if $resval;
        if(defined($valp)) {# q=>0 & p=0/1
          return 0; # stay 0
        } else {# q=>0 & p=?
          return 0; # stay 0
        }
      } else {# q=>?
        die "assert(eq=0) as q=>? would imped it to be 1" if $resval;
        if(defined($valp) && $valp == 1) {# q=>? & p=1
          return 0; # stay 0
        } elsif(defined($valp)) {# q=>? & p=0
          return 0; # stay 0
        } else {# q=>? & p=?
          return undef;
        }
      }
    }
  } elsif($p->[0] == $t && $q->[0] == $t) { # p & q
    # cases when p xor q didn't change were handled as singleton events
    # so check here only the case when none changed:
    if(&sameval($valp, &lastval($ref_p, $t)) &&
       &sameval($valq, &lastval($ref_q, $t))) { return $resval; } # nothing
    else {
      if(defined($valp) && $valp == 0 && defined($valq) && $valq == 0) {
        # p=>0 & q=>0
        return 0; # stay or become 0
      } elsif(defined($valp) && $valp == 0 && defined($valq) && $valq == 1) {
        # p=>0 & q=>1
        die "assert(eq=0) as q was 0" if $resval;
        return 0; # stay 0
      } elsif(defined($valp) && $valp == 1 && defined($valq) && $valq == 0) {
        # p=>1 & q=>0
        die "assert(eq=0) as p was 0" if $resval;
        return 0; # stay 0
      } elsif(defined($valp) && $valp == 1 && defined($valq) && $valq == 1) {
        # p=>1 & q=>1
        die "assert(eq=0) as p was 0" if $resval;
	      return &eq_lookahead($t, $ref_p, $ref_q);
      } elsif(defined($valp) && $valp == 0 && !defined($valq)) {
        # p=>0 & q=>?
        die "assert(eq=0) as q=>? would imped it to be 1" if $resval;
        return 0;
      } elsif(defined($valp) && $valp == 1 && !defined($valq)) {
        # p=>1 & q=>?
        die "assert(eq=0) as p was 0" if $resval;
        if(&lastval($ref_q, $t) == 1) {
          return 0;
        } else {
          return undef;
        }
      } elsif(!defined($valp) && defined($valq) && $valq == 0) {
        # p=>? & q=>0
        die "assert(eq=0) as it cannot be 1 until q=>0" if $resval;
        return 0;
      } elsif(!defined($valp) && defined($valq) && $valq == 1) {
        # p=>? & q=>1
        die "assert(eq=0) as q was 0" if $resval;
        if(&lastval($ref_p, $t) == 1) {
          return 0;
        } else { # p was 0
          return undef;
        }
      } else {
        # p=>? & q=>?
        return undef;
      }
    }
  }
  die "eq2: void return";
}

sub ends_lookahead() {
  my ($t, $ref_p, $ref_q) = @_;
  if(&left($ref_p, $ref_q, $t, 0, 0)) {
    return 0;
  } elsif(&right($ref_p, $ref_q, $t, 0, 0)) {
    return 0;
  } elsif(&sync($ref_p, $ref_q, $t, 0, 0)) {
    return 1;
  } else {
    return undef;
  }
}

# true during the intervals of p which end an interval of q
sub ends2() {
  my ($t, $ref_p, $ref_q, $ref_res, $resval) = @_;
  if($t == 0) { return 0; }
  my $p = &tsval($ref_p, $t);
  my $q = &tsval($ref_q, $t);
  my $valp = $p->[1];
  my $valq = $q->[1];
  #print STDERR "tsval(p,$t)=[$p->[0],$valp], val(q,$t)=[$q->[0],$valq]\n";
  if($p->[0] == $t && $q->[0] < $t ||
     $p->[0] == $t && $q->[0] == $t && &sameval($valq, &lastval($ref_q, $t))) {
    # only p
    if(&sameval($valp, &lastval($ref_p, $t))) { return $resval; } # nothing
    else {
      if(defined($valp) && $valp == 1) {# p=>1
        die "assert(ends=0) as p was 0" if $resval;
        if(defined($valq) && $valq == 1) {# p=>1 & q=1
	  return &ends_lookahead($t, $ref_p, $ref_q);
        } elsif(defined($valq)) {# p=>1 & q=0
          return 0; # stay 0
        } else {# p=>1 & q=?
          return undef;
        }
      } elsif(defined($valp) && $valp == 0) {# p=>0 & q=0/1/?
        if(defined($valq) && $valq == 1) {# p=>0 & q=1
          die "assert(ends=0) as p=>0 would imped it to be 1" if $resval;
          return 0; # stay 0
        } elsif(defined($valq)) {# p=>0 & q=0
          die "assert(ends=0) as q was 0" if $resval;
          return 0; # stay 0
        } else {# p=>0 & q=?
          die "assert(ends=0) as q=>? would imped it to be 1" if $resval;
          return 0; # stay 0
        }
      } else {# p=>?
        die "assert(ends=0) as p=>? would imped it to be 1" if $resval;
        if(defined($valq) && $valq == 1) {# p=>? & q=1
          return undef;
        } elsif(defined($valq)) {# p=>? & q=0
          return 0; # stay 0
        } else {# p=>? & q=?
          return undef;
        }
      }
    }
  } elsif($p->[0] < $t && $q->[0] == $t ||
          $p->[0] == $t && $q->[0] == $t && &sameval($valp, &lastval($ref_p, $t))) {
    # only q
    if(&sameval($valq, &lastval($ref_q, $t))) { return $resval; } # nothing
    else {
      if(defined($valq) && $valq == 1) {# q=>1
        die "assert(ends=0) as q was 0" if $resval;
        if(defined($valp)) {# q=>1 & p=0/1
          return 0; # stay 0
        } else {# q=>1 & p=?
          return undef;
          # NB: even though you know that between is 0 right now,
          # this value may not last until next()
        }
      } elsif(defined($valq) && $valq == 0) {# q=>0 & p=0/1/?
        if(defined($valp)) {# q=>0 & p=0/1
          die "assert(ends=0) as q=>0 would imped it to be 1" if $resval;
          return 0; # stay 0
        } else {# q=>0 & p=?
          die "p could not be ? when q was 1";
        }
      } else {# q=>?
        die "assert(ends=0) as q=>? would imped it to be 1" if $resval;
        if(defined($valp) && $valp == 1) {# q=>? & p=1
          return 0; # stay 0
          # NB: *whether q was 0 or 1 before) this p interval is compromised,
          # so a new one must start for ends to become 1
        } elsif(defined($valp)) {# q=>? & p=0
          return 0; # stay 0
        } else {# q=>? & p=?
          return undef;
        }
      }
    }
  } elsif($p->[0] == $t && $q->[0] == $t) { # p & q
    # cases when p xor q didn't change were handled as singleton events
    # so check here only the case when none changed:
    if(&sameval($valp, &lastval($ref_p, $t)) &&
       &sameval($valq, &lastval($ref_q, $t))) { return $resval; } # nothing
    else {
      if(defined($valp) && $valp == 0 && defined($valq) && $valq == 0) {
        # p=>0 & q=>0
        return 0; # stay or become 0
      } elsif(defined($valp) && $valp == 0 && defined($valq) && $valq == 1) {
        # p=>0 & q=>1
        die "assert(ends=0) as q was 0" if $resval;
        return 0; # stay 0
      } elsif(defined($valp) && $valp == 1 && defined($valq) && $valq == 0) {
        # p=>1 & q=>0
        die "assert(ends=0) as p was 0" if $resval;
        return 0; # stay 0
      } elsif(defined($valp) && $valp == 1 && defined($valq) && $valq == 1) {
        # p=>1 & q=>1
        die "assert(ends=0) as p was 0" if $resval;
        return 0;
      } elsif(defined($valp) && $valp == 0 && !defined($valq)) {
        # p=>0 & q=>?
        die "assert(ends=0) as q=>? would imped it to be 1" if $resval;
        return 0; # stay 0
      } elsif(defined($valp) && $valp == 1 && !defined($valq)) {
        # p=>1 & q=>?
        die "assert(ends=0) as p was 0" if $resval;
        if(&lastval($ref_q, $t) == 1) {
          return undef;
        } else {
          return 0; # stay 0
        }
      } elsif(!defined($valp) && defined($valq) && $valq == 0) {
        # p=>? & q=>0
        die "assert(ends=0) as p=>? would imped it to be 1" if $resval;
        return 0;
      } elsif(!defined($valp) && defined($valq) && $valq == 1) {
        # p=>? & q=>1
        die "assert(ends=0) as q was 0" if $resval;
        return undef;
        # NB: even though you know that between is 0 right now,
        # this value may not last until next()
      } else {
        # p=>? & q=>?
        return undef;
      }
    }
  }
  die "ends2: void return";
}

# true during the intervals of p which are met by an interval of q
sub met2() {
  my ($t, $ref_p, $ref_q, $ref_res, $resval) = @_;
  if($t == 0) { return 0; }
  my $p = &tsval($ref_p, $t);
  my $q = &tsval($ref_q, $t);
  my $valp = $p->[1];
  my $valq = $q->[1];
  #print STDERR "tsval(p,$t)=[$p->[0],$valp], val(q,$t)=[$q->[0],$valq]\n";
  if($p->[0] == $t && $q->[0] < $t ||
     $p->[0] == $t && $q->[0] == $t && &sameval($valq, &lastval($ref_q, $t))) {
    # only p
    if(&sameval($valp, &lastval($ref_p, $t))) { return $resval; } # nothing
    else {
      if(defined($valp) && $valp == 1) {# p=>1
        die "assert(met=0) as p was 0" if $resval;
        if(defined($valq)) {# p=>1 & q=0/1
          return 0; # stay 0
        } else {# p=>1 & q=?
          return undef;
        }
      } elsif(defined($valp) && $valp == 0) {# p=>0 & q=0/1/?
        if(defined($valq)) {# p=>0 & q=0/1
          return 0; # stay or become 0
        } else {# p=>0 & q=?
          return 0; # stay or become 0
        }
      } else {# p=>?
        if(defined($valq)) {# p=>? & q=0/1
          if($resval) {
            return undef;
          } else {
            return 0; # stay 0
          }
        } else {# p=>? & q=?
          return undef;
        }
      }
    }
  } elsif($p->[0] < $t && $q->[0] == $t ||
          $p->[0] == $t && $q->[0] == $t && &sameval($valp, &lastval($ref_p, $t))) {
    # only q
    if(&sameval($valq, &lastval($ref_q, $t))) { return $resval; } # nothing
    else {
      if(defined($valq) && $valq == 1) {# q=>1
        if(defined($valp)) {# q=>1 & p=0/1
          return $resval; # no change
        } else {# q=>1 & p=?
          die "assert(met=0) as it cannot be 1 when p=?" if $resval;
          return 0; # stay 0
        }
      } elsif(defined($valq) && $valq == 0) {# q=>0 & p=0/1/?
        if(defined($valp)) {# q=>0 & p=0/1
          return $resval; # no change
        } else {# q=>0 & p=?
          die "assert(met=0) as it cannot be 1 when p=?" if $resval;
          return 0; # stay 0
        }
      } else {# q=>?
        if(defined($valp)) {# q=>? & p=0/1
          return $resval; # no change
        } else {# q=>? & p=?
          return undef;
        }
      }
    }
  } elsif($p->[0] == $t && $q->[0] == $t) { # p & q
    # cases when p xor q didn't change were handled as singleton events
    # so check here only the case when none changed:
    if(&sameval($valp, &lastval($ref_p, $t)) &&
       &sameval($valq, &lastval($ref_q, $t))) { return $resval; } # nothing
    else {
      if(defined($valp) && $valp == 0 && defined($valq) && $valq == 0) {
        # p=>0 & q=>0
        return 0; # stay or become 0
      } elsif(defined($valp) && $valp == 0 && defined($valq) && $valq == 1) {
        # p=>0 & q=>1
        return 0; # stay or become 0
      } elsif(defined($valp) && $valp == 1 && defined($valq) && $valq == 0) {
        # p=>1 & q=>0
        die "assert(met=0) as p was 0" if $resval;
        return 1;
      } elsif(defined($valp) && $valp == 1 && defined($valq) && $valq == 1) {
        # p=>1 & q=>1
        die "assert(met=0) as p was 0" if $resval;
        return 0; # stay 0
      } elsif(defined($valp) && $valp == 0 && !defined($valq)) {
        # p=>0 & q=>?
        return 0; # stay or become 0
      } elsif(defined($valp) && $valp == 1 && !defined($valq)) {
        # p=>1 & q=>?
        die "assert(met=0) as p was 0" if $resval;
        if(&lastval($ref_q, $t) == 1) {
          return undef;
        } else {
          return 0;
        }
      } elsif(!defined($valp) && defined($valq) && $valq == 0) {
        # p=>? & q=>0
        if($resval == 1) {
          return undef;
        }
        if(&lastval($ref_p, $t) == 1) {
          return 0; # stay 0
        } else {
          return undef;
        }
      } elsif(!defined($valp) && defined($valq) && $valq == 1) {
        # p=>? & q=>1
        if($resval == 1) {
          return undef;
        }
        return 0; # stay 0
      } else {
        # p=>? & q=>?
        return undef;
      }
    }
  }
  die "met2: void return";
}

sub meets_lookahead() {
  my ($t, $ref_p, $ref_q) = @_;
  my $tp0 = &next_val($t, $ref_p, 0);
  if(!defined($tp0)) {
    return undef;
  }
  my $tsq = &tsval($ref_q, $tp0);
  my $oldq = &lastval($ref_q, $tp0);
  # check q at tp0:
  if($tsq->[0] == $tp0 && defined($tsq->[1]) && $tsq->[1] == 1 && defined($oldq) && $oldq == 0) {
    # q=>1
    return 1;
  }
  if($tsq->[0] == $tp0 && !defined($tsq->[1]) && defined($oldq) && $oldq == 1) {
    # q=>? and was 1
    return 0;
  }
  if(defined($tsq->[1])){
    # q=0/1 or q=>0
    return 0;
  }
  # q=? or q=>? and was 0
  return undef;
}

# true during the intervals of p which meet an interval of q
sub meets2() {
  my ($t, $ref_p, $ref_q, $ref_res, $resval) = @_;
  my $p = &tsval($ref_p, $t);
  my $q = &tsval($ref_q, $t);
  my $valp = $p->[1];
  my $valq = $q->[1];
  #print STDERR "tsval(p,$t)=[$p->[0],$valp], val(q,$t)=[$q->[0],$valq]\n";
  if($t == 0) {
    if (defined($valp) && $valp == 0) {
      return 0;
    } elsif ($valp == 1 && defined($valq)) {
      return &meets_lookahead($t, $ref_p, $ref_q);
    } else {
      return undef;
    }
  }
  if($p->[0] == $t && $q->[0] < $t ||
     $p->[0] == $t && $q->[0] == $t && &sameval($valq, &lastval($ref_q, $t))) {
    # only p
    if(&sameval($valp, &lastval($ref_p, $t))) { return $resval; } # nothing
    else {
      if(defined($valp) && $valp == 1) {# p=>1
        die "assert(meets=0) as p was 0" if $resval;
        if(defined($valq)) {# p=>1 & q=0/1
	  return &meets_lookahead($t, $ref_p, $ref_q);
        } else {# p=>1 & q=?
          return undef;
        }
      } elsif(defined($valp) && $valp == 0) {# p=>0 & q=0/1/?
        if(defined($valq)) {# p=>0 & q=0/1
          die "assert(meets=0) as q=0/1 would imped it to be 1" if $resval;
          return 0; # stay 0
        } else {# p=>0 & q=?
          die "assert(meets=0) as q=? would imped it to be 1" if $resval;
          return 0; # stay 0
        }
      } else {# p=>?
        die "assert(meets=0) as p=>? would imped it to be 1" if $resval;
        if(defined($valq)) {# p=>? & q=0/1
          die "assert(p was 0) as p was 1 then ? would imped meets to be 0"
            if &lastval($ref_p, $t) == 1;
          return undef;
        } else {# p=>? & q=?
          return undef;
        }
      }
    }
  } elsif($p->[0] < $t && $q->[0] == $t ||
          $p->[0] == $t && $q->[0] == $t && &sameval($valp, &lastval($ref_p, $t))) {
    # only q
    if(&sameval($valq, &lastval($ref_q, $t))) { return $resval; } # nothing
    else {
      if(defined($valq) && $valq == 1) {# q=>1
        if(defined($valp) && $valp == 1) {# q=>1 & p=1
        return $resval; # no change
        } elsif(defined($valp)) {# q=>1 & p=0
          die "assert(meets=0) as p is 0" if $resval;
          return 0; # stay 0
        } else {# q=>1 & p=?
          die "p=? cannot happen as it would imply meets=?"
        }
      } elsif(defined($valq) && $valq == 0) {# q=>0 & p=0/1/?
        if(defined($valp) && $valp == 1) {# q=>0 & p=1
          return $resval; # no change
        } elsif(defined($valp)) {# q=>0 & p=0
          return 0; # stay 0
        } else {# q=>0 & p=?
          die "p=? cannot happen as it would imply meets=?"
        }
      } else {# q=>?
        die "assert(meets=0) as q=>? would imped it to be 1" if $resval;
        if(defined($valp) && $valp == 1) {# q=>? & p=1
          die "assert(p=0) as q=>? while p is 1 would imped meets to be 0";
        } elsif(defined($valp)) {# q=>? & p=0
          return 0; # stay 0
        } else {# q=>? & p=?
          die "p=? cannot happen as it would imply meets=?"
        }
      }
    }
  } elsif($p->[0] == $t && $q->[0] == $t) { # p & q
    # cases when p xor q didn't change were handled as singleton events
    # so check here only the case when none changed:
    if(&sameval($valp, &lastval($ref_p, $t)) &&
       &sameval($valq, &lastval($ref_q, $t))) { return $resval; } # nothing
    else {
      if(defined($valp) && $valp == 0 && defined($valq) && $valq == 0) {
        # p=>0 & q=>0
        die "assert(meets=0) as p=>0 & q=>0 would be anticipated" if $resval;
        return 0;
      } elsif(defined($valp) && $valp == 0 && defined($valq) && $valq == 1) {
        # p=>0 & q=>1
        die "assert(meets=1)" if $resval == 0 &&
          !($#$ref_p == 1 && $$ref_p[0][1] == 1);
        # NB: if p started 1 and becomes 0 for the 1st time, meets=0
        return 0; # become 0
      } elsif(defined($valp) && $valp == 1 && defined($valq) && $valq == 0 ||
              defined($valp) && $valp == 1 && defined($valq) && $valq == 1) {
        # p=>1 & q=>0 | p=>1 & q=>1
        die "assert(meets=0) as p was 0" if $resval;
	      return &meets_lookahead($t, $ref_p, $ref_q);
      } elsif(defined($valp) && $valp == 0 && !defined($valq)) {
        # p=>0 & q=>?
        die "assert(meets=0)" if $resval;
        die "assert(q was 1)" if &lastval($ref_q, $t) == 0 &&
          !($#$ref_p == 1 && $$ref_p[0][1] == 1);
        # NB: if p started 1 and becomes 0 for the 1st time, meets=0 indep. of q
        return 0;
      } elsif(defined($valp) && $valp == 1 && !defined($valq)) {
        # p=>1 & q=>?
        die "assert(meets=0) as p was 0" if $resval;
        return undef;
      } elsif(!defined($valp) && defined($valq) && $valq == 0) {
        # p=>? & q=>0
        die "assert(meets=0) as it cannot be 1 until p=>?" if $resval;
        die "assert(p was 0) as it cannot be 1 until p=>?" if &lastval($ref_p, $t) == 1;
        return undef;
      } elsif(!defined($valp) && defined($valq) && $valq == 1) {
        # p=>? & q=>1
        die "assert(meets=0) as it cannot be 1 until p=>?" if $resval;
        die "assert(p was 0) as it cannot be 1 until p=>?" if &lastval($ref_p, $t) == 1;
        return undef;
      } else {
        # p=>? & q=>?
        return undef;
      }
    }
  }
  die "meets2: void return";
}

# ------------------------------------------------------
# Prefix notations for duration operators

# prefix notation for p > T`
sub GT() {
  my ($p, $T) = @_;
  return [&gt($T), $p];
}

# prefix notation for p <= T
sub LE() {
  my ($p, $T) = @_;
  return [&le($T), $p];
}

# prefix notation for p >= T`
sub GE() {
  my ($p, $T) = @_;
  return [&ge($T), $p];
}

# prefix notation for p < T
sub LT() {
  my ($p, $T) = @_;
  return [&lt($T), $p];
}

# prefix notation for p >! T`
sub GTrt() {
  my ($p, $T) = @_;
  return [&gtRT($T), $p];
}

# prefix notation for p >=! T`
sub GErt() {
  my ($p, $T) = @_;
  return [&geRT($T), $p];
}

# ------------------------------------------------------
# Derived LTL/MTL operators

sub O() {
  my ($p) = @_;
  return &since([&true], $p);
}

sub H() {
  my ($p) = @_;
  return [&not, &O([&not, $p])];
}

sub F() {
  my ($p) = @_;
  return &until([&true], $p);
}

sub G() {
  my ($p) = @_;
  return [&not, &F([&not, $p])];
}

sub init() {
  my ($p) = @_;
  return &occ(&orig, $p);
}

sub H_le() {
  my ($p, $T) = @_;
  return [&or, [&gtRTa($T), $p], &init($p)];
}

sub O_le() {
  my ($p, $T) = @_;
  return [&not, &H_le($p, $T)];
}

# ------------------------------------------------------
# Other derived operators

# p goes up (p=>1); may include t=0
sub up0() {
  my ($p) = @_;
  return [&geRT(1), $p];
  #return [&and, $p, [&not, [&delay(1), $p]]];
}

# p goes down (p=>0); may include t=0
sub dn0() {
  my ($p) = @_;
  #return [&geRT(1), [&not, $p]];
  return &up0([&not, $p]);
}

# p goes up (p=>1); excludes t=0
sub up() {
  my ($p) = @_;
  return [&and, &up0($p), &step(1)];
}

# p goes down (p=>0); excludes t=0
sub dn() {
  my ($p) = @_;
  return &up([&not, $p]);
  #return [&and, &dn0($p), &step(1)];
}

# p switches value (p=>0/1)
sub sw() {
  my ($p) = @_;
  return [&or, &up($p), &dn($p)];
}

# return all the intervals of p, cut at T if longer
sub cut() {
  my ($p, $T) = @_;
  return [&or, [&le($T), $p], [&gtRT($T), $p]];
}

# prolonges each interval of p by T
sub recent() {
  my ($p, $T) = @_;
  return [&or, $p, &cut(&met([&not, $p], $p), $T)];
}

# intervals of p "far away" (i.e. separated by at least T) from intervals of q
sub far() {
  my ($p, $q, $T) = @_;
  return &starts($p, &during( &recent($p, $T), [&not, &recent($q, $T)]));
}

# the first interval of p starting or during q
sub first() {
  my ($p, $q) = @_;
  return &starts($p, &occ($p, $q));
}

# fill holes between p's wihtin q
sub fill() {
  my ($p, $q) = @_;
  return [&or, [&and, $p, $q], &during( [&not, $p], $q)];
}

# collapse all p's during q
sub flat() {
  my ($p, $q) = @_;
  my $d;
  return [&or, $d=&during( $p, $q), &during( [&not, $d], $q)];
}

# extends flat rightwards to end of slot q if p reaches the end of slot
sub flat_right() {
  my ($p, $q) = @_;
  return [&and, &occ(&up($p), $q), &fill($p, $q)];
}

# step function, becoming true at T
sub step() {
  my ($T) = @_;
  #return [&wave($T,0,0,0)];
  return [&delay($T), [&true]];
}

# true only initially, at the origin of time (t=0)
sub orig() {
  return [&not, &step(1)];
}

# s1, then s2 occur (for the 1st time) in the slot
sub occ_before() {
  my ($s1, $s2, $slot) = @_;
  return [&and, &occ($s1, $slot), [&and, [&not, &occ($s2, $slot)], &ex($s2, $slot)]];
}

# ------------------------------------------------------
# Slot operators, useful e.g. for daily activities

# wave signal which is 1 every day between daytimes from and to
# NB: DST-safe! (daylight saving time)
sub slot_dst_2017() {
  my ($from, $to) = @_;
  my $ts2 = 1490482800000; # 26/03/2017 00:00:00 (start summer time)
  my $ts3 = 1509228000000; # 29/10/2017 00:00:00 (end summer time)
  return &slot_2017($from, $to, $ts2, $ts3);
}

sub slot_dst_2018() {
  my ($from, $to) = @_;
  my $ts2 = 1521932400000; # 25/03/2018 00:00:00 (start summer time)
  my $ts3 = 1540677600000; # 28/10/2018 00:00:00 (end summer time)
  return &slot_2018($from, $to, $ts2, $ts3);
}

sub slot_2017() {
  my ($from, $to, $tsummer, $twinter) = @_;
  my $ts0 = 1483225200000; # 01/01/2017 00:00:00
  my $ts1 = 1514761200000; # 01/01/2018 00:00:00
  return &slot($from, $to, $ts0, $ts1, $tsummer, $twinter);
}

sub slot_2018() {
  my ($from, $to, $tsummer, $twinter) = @_;
  my $ts0 = 1514761200000; # 01/01/2018 00:00:00
  my $ts1 = 1546297200000; # 01/01/2019 00:00:00
  return &slot($from, $to, $ts0, $ts1, $tsummer, $twinter);
}

# NB: optionnally DST-safe (daylight saving time)
sub slot() {
  my ($from, $to, $ts0, $ts1, $tsummer, $twinter) = @_;
  my $t1 = $from < $to? $to - $from: 24*60*60*1000 + $to - $from;
  my $t0 = 24*60*60*1000 - $t1;
  #return [&delay($ts0 + $to), [&wave($t0, $t1, 0, $ts1 - $ts0)]];
  if(!defined($tsummer)) {
    return [&wave($t0, $t1, $ts0 + $to, $ts1)];
  } else {
    return
      [&or, [&or, [&wave($t0, $t1, $ts0 + $to, $tsummer)],
                  [&wave($t0, $t1, $tsummer - (24+1)*60*60*1000 + $to, $twinter)]],
            [&wave($t0, $t1, $twinter - (24-1)*60*60*1000 + $to, $ts1)]];
  }
}

# ------------------------------------------------------
# N-ary operators (handling a list of signals)

sub lreduce() { # associate left: (a+b)+c
  my ($f, @lst) = @_;
  if($#lst < 0) { die "no args"; }
  my $res = $lst[0];
  for(my $i = 1; $i <= $#lst; $i++) {
    $res = &$f($res, $lst[$i]);
  }
  return $res;
}

sub rreduce() { # associate right: a+(b+c)
  my ($f, @lst) = @_;
  if($#lst < 0) { die "no args"; }
  my $res = $lst[$#lst];
  for(my $i = $#lst - 1; $i >= 0 ; $i--) {
    $res = &$f($lst[$i], $res);
  }
  return $res;
}

# nary or
sub any() {
  my (@lst) = @_;
  return &lreduce(sub {my ($p, $q) = @_; return [&or, $p, $q]}, @lst);
}

# nary and
sub all() {
  my (@lst) = @_;
  return &lreduce(sub {my ($p, $q) = @_; return [&and, $p, $q]}, @lst);
}

# nary or_up
sub any_up() {
  my (@lst) = @_;
  return &any(map {&up($_)} @lst);
}

sub any_dn() {
  my (@lst) = @_;
  return &any(map {&dn($_)} @lst);
}

sub any_sw() {
  my (@lst) = @_;
  return &any(map {&sw($_)} @lst);
}

# ------------------------------------------------------
# Result of the load
(
# Requires
{}, # nothing but builtins
# Provides
{
# Allen logic operators
"during" => [0,2,
"during(p,q) selects the states of p strictly contained in some state of q,
{[t,t') in p | [t'',t''') in q & t''<t<t'<t'''}"],
"contains" => [0,2,
"contains(p,q) selects the states of p strictly containing some state of q,
{[t,t') in p | [t'',t''') in q & t<t''<t'''<t'}"],
"over" => [0,2,
"over(p,q) selects the intersections between states of p overlapping some state
of q,
{[t'',t') | [t,t') in p & [t'',t''') in q & t<t''<t'<t'''}"],
"overlaps" => [0,2,
"overlaps(p,q) selects the states of p overlapping some state of q,
{[t,t') in p | [t'',t''') in q & t<t''<t'<t'''}"],
"overlapped" => [0,2,
"overlapped(p,q) selects the states of p overlapped by some state of q,
{[t,t') in p | [t'',t''') in q & t''<t<t'''<t'}"],
"starts" => [0,2,
"starts(p,q) selects the states of p starting some state of q,
{[t,t') in p | [t,t'') in q & t'<t''}"],
"started" => [0,2,
"started(p,q) selects the states of p started by some state of q,
{[t,t') in p | [t,t'') in q & t''<t'}"],
"ends" => [0,2,
"ends(p,q) selects the states of p ending some state of q,
{[t,t') in p | [t'',t') in q & t''<t}"],
"ended" => [0,2,
"ended(p,q) selects the states of p ended by some state of q,
{[t,t') in p | [t'',t') in q & t<t''}"],
"eq" => [0,2,
"eq(p,q) selects the states of p equal to some state of q,
{[t,t') in p | [t,t') in q}"],
"meets" => [0,2,
"meets(p,q) selects the states of p meeting some state of q,
{[t,t') in p | [t',t'') in q}"],
"met" => [0,2,
"met(p,q) selects the states of p met by some state of q,
{[t,t') in p | [t'',t) in q}"],
"between" => [0,2,
"between(p,q) selects the intervals between a state in p and the next state in q,
{[t',t'') | [t,t') in p & [t'',t''') in q & t'<t'' &
            any later state of p ends strictly after t'' &
            any earlier state of q starts strictly before t'}"],
"before" => [0,2,
"before(p,q) selects the states of p immediately before some state of q,
{[t,t') in p | [t',t'') in between(p,q)}"],
"after" => [0,2,
"after(p,q) selects the states of p immediately after some state of q,
{[t,t') in p | [t'',t') in between(p,q)}"],
"btwin" => [0,2,
"btwin(p,q) selects the quiet intervals between a state in p and the next state
in q,
{[t',t'') | [t,t') in p & [t'',t''') in q & t'<t'' &
            p is 0 on [t',t'') & q is 0 on (t',t'')"],
"btw" => [0,2,
"btw(p,q) selects the fully quiet intervals between a state in p and the next
state in q,
{[t',t'') | [t,t') in p & [t'',t''') in q & t'<t'' &
            p is 0 on [t',t''] & q is 0 on [t',t'')"],
"holds" => [0,2,
"holds(p,q) selects the states of q where p always holds,
{[t,t') in q | forall t'' in [t,t') . p(t'')}"],
"ex" => [0,2,
"ex(p,q) selects the states of q where p occurs at least once,
{[t,t') in q | exists t'' in [t,t') . p(t'')}"],
"occ" => [0,2,
"occ(p,q) selects the ends of states of q where p has already occurred,
{[t'',t') | [t,t') in q & exists t'' in [t,t') . p(t'') & p is 0 on [t,t'')}"],
# Duration operators in functional notation
"LT" => [1,1, "LT[T](p) is the prefix notation for p < T"],
"LE" => [1,1, "LE[T](p) is the prefix notation for p <= T"],
"GT" => [1,1, "GT[T](p) is the prefix notation for p > T"],
"GE" => [1,1, "GE[T](p) is the prefix notation for p >= T"],
"GTrt" => [1,1, "GTrt[T](p) is the prefix notation for p >! T"],
"GErt" => [1,1, "GErt[T](p) is the prefix notation for p >=! T"],
# LTL/MTL operators
"O" => [0,1, "O(p) is the Once operator in LTL,
O(p)(t) <-> exists t'<=t . p(t')"],
"H" => [0,1, "H(p) is the Historically operator in LTL,
H(p)(t) <-> forall t'<=t . p(t')"],
"F" => [0,1, "F(p) is the Finally operator in LTL,
F(p)(t) <-> exists t'>=t . p(t')"],
"G" => [0,1, "G(p) is the Globally operator in LTL,
G(p)(t) <-> forall t'>=t . p(t')"],
"O_le" => [1,1, "O_le[T](p) is the bounded Once[0,T] operator in MTL,
O_le[T](p)(t) <-> exists t'. t-t' in [0,T] and p(t')"],
"H_le" => [1,1, "H_le[T](p) is the bounded Historically[0,T] operator in MTL,
H_le[T](p)(t) <-> forall t'. t-t' in [0,T] -> p(t')"],
# Event generators
"up" => [0,1,
"up(p) is true whenever p starts being 1, excluding t=0,
{[t,t+1) | [t,t') in p & t>0}"],
"dn" => [0,1,
"dn(p) is true whenever p starts being 0, excluding t=0,
{[t,t+1) | [t',t) in p}"],
"up0" => [0,1,
"up0(p) is true whenever p starts being 1, possibly including t=0,
{[t,t+1) | [t,t') in p}"],
"dn0" => [0,1,
"dn0(p) is true whenever p starts being 0, possibly including t=0,
{[t,t+1) | [t',t) in p or (t=0 & not p(t))}"],
"sw" => [0,1,
"sw(p) is true whenever p switches value,
sw(p)(t) <-> up(t) or dn(t)"],
# Slot operators
"slot" => [6,0,
"slot[Tf,Tt,Ts,Te,S,W] generates a daily slot lasting each day from Tf to Tt,
starting at Ts, ending at Te, and switching to summer time as S and back at W"],
"slot_dst_2017" => [2,0,
"slot_dst_2017[Tf,Tt] generates a daily slot for the whole year 2017, lasting
each day from Tf to Tt"],
"slot_dst_2018" => [2,0,
"slot_dst_2017[Tf,Tt] generates a daily slot for the whole year 2018, lasting
each day from Tf to Tt"],
# N-ary operators
"all" => [0, undef, "all(s1,...sN) is an N-ary boolean and"],
"any" => [0, undef, "any(s1,...sN) is an N-ary boolean or"],
"any_up" => [0, undef,
"any_up(s1,...sN) is true whenever some of the signals becomes 1"],
"any_dn" => [0, undef,
"any_dn(s1,...sN) is true whenever some of the signals becomes 0"],
"any_sw" => [0, undef,
"any_sw(s1,...sN) is true whenever some of the signals switches its value"],
# Basic derived operators
"init" => [0,1,
"init(p) selects the initial state of p (starting at t=0), if there is one,
{[0,t') | [0,t') in p}"],
"step" => [1,0,
"step[T] is the step function, 0 until T and 1 starting at T,
{[T,inf)}"],
"orig" => [0,0,
"orig() is true only at the origin (at t=0),
{[0,1)}"],
# Other derived operators
"cut" => [1,1,
"cut[T](p) selects all the states of p, shortened to T if longer,
{[t,min(t',t+T)) | [t,t') in p}"],
"recent" => [1,1,
"recent[T](p) is true whenever p has occurred in the last T,
recent[T](p)(t) <-> exists t'>0 in [t-T,t] . p(t')"],
"far" => [1,2,
"far[T](p,q) select states of p that are further (> T) away from any state in q"],
"first" => [0,2,
"first(p,q) selects the first state of p starting or during some state of q"],
"fill" => [0,2, "fill(p,q) fills holes between p's within q"],
"flat" => [0,2, "flat(p,q) collapses all p's during q"],
"flat_right" => [0,2,
"flat_right(p,q) extends flat rightwards to end of slot q if p reaches the
end of slot"],
"occ_before" => [0,3,
"occ_before(p,q,slot) is true between the moments when p, then q occur for the
1st time in the slot"],
},
# Contexts
[]
)
