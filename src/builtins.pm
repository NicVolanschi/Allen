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
# Library of operators built into the Allen language
#

# ------------------------------------------------------
# Boolean operators

sub false() {
  return \&false0;
}

sub false0() {
  my ($t, $ref_res, $resval) = @_;
  return 0;
}

sub true() {
  return \&true0;
}

sub true0() {
  my ($t, $ref_res, $resval) = @_;
  return 1;
}

# identity: id(s) == s
sub id() {
  return \&id1;
}

sub id1() {
  my ($t, $ref_p, $ref_res, $resval) = @_;
  my $valp = &val($ref_p, $t);
  return $valp;
}

sub not() {
  return \&not1;
}

sub not1() {
  my ($t, $ref_p, $ref_res, $resval) = @_;
  #if($t == 0) { # initially
  #  return $$ref_p[0][1] == 1? 0: 1; # NB: !1="", not 0 !!
  #}
  my $valp = &val($ref_p, $t);
  return not1_pointwise($valp);
}

# not of a point value
sub not1_pointwise() {
  my ($x) = @_;
  if(!defined($x)) {
    return undef;
  } elsif($x == 1) {
    return 0; # NB: !1="", not 0 !!
  } else {
    return 1;
  }
}

sub or() {
  return \&or2;
}

sub or2() {
  my ($t, $ref_p, $ref_q, $ref_res, $resval) = @_;
  my $valp = &val($ref_p, $t);
  my $valq = &val($ref_q, $t);
  #if($t == 0) { return $valp || $valq; }
  return or2_pointwise($valp, $valq);
}

# or between two point values
sub or2_pointwise() {
  my ($x, $y) = @_;
  if(defined($x) && $x == 1 || defined($y) && $y == 1) {
  return 1; # 1 beats ?
  } elsif(defined($x) && defined($y)) { # 0 or 0
    return 0;
  } else { # 0 or ?, ? or 0, ? or ?`
    return undef;
  }
}

sub and() {
  return \&and2;
}

sub and2() {
  my ($t, $ref_p, $ref_q, $ref_res, $resval) = @_;
  my $valp = &val($ref_p, $t);
  my $valq = &val($ref_q, $t);
  #if($t == 0) { return $valp && $valq; }
  return and2_pointwise($valp, $valq);
}

# and between two point values
sub and2_pointwise() {
  my ($x, $y) = @_;
  if(defined($x) && $x == 1 && defined($y) && $y == 1) {
  return 1;
} elsif(defined($x) && $x == 0 || defined($y) && $y == 0) { # 0 beats ?
    return 0;
  } else { # 1 and ?, ? and 1, ? and ?`
    return undef;
  }
}

# ------------------------------------------------------
# Operators adapted from LTL logic

sub since() {
  my ($p, $q) = @_;
  return [\&ssince2, $p, $q];
}

sub wsince() {
  my ($p, $q) = @_;
  return [\&wsince2, $p, $q];
}

sub until() {
  my ($p, $q) = @_;
  return [\&until2, $p, $q];
}

# Consider weak until equivalent to until, as in LTL3
# TODO: implement differently when called at the "end of time", i.e. after
# processing of a complete log file.
sub wuntil() {
  my ($p, $q) = @_;
  return [\&until2, $p, $q];
}

sub wsince2() {
  return &since2(@_, 0);
}

sub ssince2() {
  return &since2(@_, 1);
}

sub since2() {
  my ($t, $ref_p, $ref_q, $ref_res, $resval, $strong) = @_;
  my $valp = &val($ref_p, $t);
  my $valq = &val($ref_q, $t);
  if (defined($valq) && $valq  == 1) { # q=1 | q=>1
    return 1;
  } elsif (defined($valq) && $valq == 0) { # q=0 | q=>0
    my $tq = &became_ts($t, $ref_q, 0);
    if ($strong && $tq == 0) {
      return 0;
    }
    if (defined($valp) && $valp == 0) { # p=0 | p=>0
      return 0;
    } elsif (!defined($valp)) { # p=? | p=>?
      my $tp0 = &lastseen_as($t, $ref_p, 0);
      # if since=0 return 0
      # if ($t > 0 && $resval == 0 || $t == 0 && $strong) { # at t=0: S=0, Z=1
      if (defined($tp0) && $tp0 > $tq) {
        return 0;
      } else {
        return undef;
      }
    } else { # p=1 | p=>1
      my $tp = &became_ts($t, $ref_p, 1);
      if ($strong) {
        return ($tq > 0 && $tp <= $tq)? 1: 0;
      } else {
        return ($tp <= $tq)? 1: 0;
      }
      # return $t > 0? $resval # unchanged
      #         : !$strong; # at t=0: S=0, Z=1
    }
  } else { # q=? | q=>?
    if (defined($valp) && $valp  == 1) {
      my $tp = &became_ts($t, $ref_p, 1);
      if (!$strong && $tp == 0) { return 1; }
      my $tq1 = &lastseen_as($t, $ref_q, 1);
      # if since=1 return 1
      # if ($t > 0 && $resval == 1 || $t == 0 && !$strong) { # at t=0: S=0, Z=1
      if (defined($tq1) && ($tq1 > 0 || !$strong) && $tp <= $tq1) {
        return 1;
      } else {
        return undef;
      }
    } elsif (defined($valp) && $valp == 0) { # p=0 | p->0
      return undef;
    } else { # p=? | p=>?
      return undef;
    }
  }

}

sub until2() {
  my ($t, $ref_p, $ref_q, $ref_res, $resval) = @_;
  #if($t == 0) { return 0; } # TODO: suppress this wrong result
  my $valp = &val($ref_p, $t);
  my $valq = &val($ref_q, $t);
  if (defined($valq) && $valq  == 1) { # q=1 | q=>1
    return 1;
  } elsif (defined($valq) && $valq == 0) {
    if (defined($valp) && $valp == 0) {
      return 0;
    } elsif (defined($valp) && $valp  == 1) {
      my $tp = &next_val($t, $ref_p, 0);
      my $tq = &next_val($t, $ref_q, 1);
      if (defined($tp) && defined($tq)) {
        return ($tq <= $tp) ? 1: 0;
      } elsif (defined($tp)) { # !defined($tq)
        if (defined(&val($ref_q, $tp))) {
          return 0;
        } else {
          return undef;
        }
      } elsif (defined($tq)) { # !defined($tp)
        if (defined(&val($ref_p, $tq)) || &tsval($ref_p, $tq)->[0] == $tq) {
          return 1;
        } else {
          return undef;
        }
      } else { # !defined(tp) & !defined(tq)
        return undef;
      }
    } else { # p=? | p=>?
      return undef;
    }
  } else { # q=? | q=>?
    return undef;
  }
}

# ------------------------------------------------------
# Delay operator

# delay a signal by T (initially 0)
sub delay() {
  my ($T) = @_;
  return sub(){ return &delay1_T(@_, $T); }
}

sub delay1_T() {
  my ($t, $ref_p, $ref_res, $resval, $T) = @_;
  if ($t == 0) { #initially
    my $valp0 = &val($ref_p, $t);
    if (!defined($valp0)) { return undef; }
    &set_timeout($T, $ref_res);
    # my $valp0 = $$ref_p[0][1];
    # die "initial value of p undefined" if !defined($valp0);
    # return $valp0;
    return 0;
  }
  my $p = &tsval($ref_p, $t);
  my $valp = $p->[1];
  # when p=>0/1, set timer; whrn p=>?, block
  if($p->[0] == $t) {
    if(&sameval($valp, &lastval($ref_p, $t))) {} # nothing
    else {
      if(defined($valp)) {# p=>0/1
        &set_timeout($t + $T, $ref_res);
      } else {# p=> ?
        return undef; # no anticipation!
        # TODO: if adding anticipation (so lookbehind), review forget policy!
      }
    }
  }
  # on timeout, change value, except the first time
  if (&timeout($t, $ref_res)) {
    &cancel_timeout($t, $ref_res);
    if ($t == $T) {
      #my $valp0 = $$ref_p[0][1];
      my $valp0 = &val($ref_p, 0);
      die "initial value of p undefined" if !defined($valp0);
      return $valp0;
      #if (!defined($valp0)) { return undef; }
      #else { return $valp0; }
      #return 0;
    } else {
      return $resval? 0: 1; # change value
    }
  } else { # no timeout, and p=>0/1 or is unchanged
    return $resval;
  }
}

# ------------------------------------------------------
# Regular signal generators

# generate a wave signal: loop (0 for T0; 1 for T1) from Ts until Te
# NB: always ends with 0, so may go shortly beyond Te.
sub wave() {
  my ($T0, $T1, $Ts, $Te) = @_;
  return sub(){ return &wave_T0_T1(@_, $T0, $T1, $Ts, $Te); }
}

sub wave_T0_T1() {
  my ($t, $ref_res, $resval, $T0, $T1, $Ts, $Te) = @_;
  if ($t == 0) { #initially
    &set_timeout($Ts + $T0, $ref_res);
    return 0;
  }
  # timeout
  my $delay = $resval == 1? $T0: $T1;
  &cancel_timeout($t, $ref_res);
  if($t + $delay < $Te || $resval == 0) { # the resval returned will be 1
    &set_timeout($t + $delay, $ref_res);
  }
  return $resval? 0: 1;
}

# generate a slot signal: every day between Ds and De, 1 from Ts until Te
# NB: always ends with 0, so may go shortly beyond De.
sub slot() {
  my ($Ts, $Te, $Ds, $De) = @_;
  die "slot: Ts=$Ts not in [0, 24hr)" if $Ts < 0 || $Ts >= 24*60*60*1000;
  die "slot: Te=$Te not in [0, 24hr)" if $Te < 0 || $Te >= 24*60*60*1000;
  die "slot: Te=Te=$Te, they must be different" if $Ts == $Te;
  my ($secDs, $minDs, $hrDs, $dayDs, $monDs, $yrDs) = localtime($Ds / 1000);
  $yrDs += 1900;
  if ($secDs != 0 || $minDs != 0 || $hrDs != 0) {
    my $err = "slot: Ds=$yrDs-$monDs-$day{Ds}T$hrDs:$minDs:$secDs is not a date, i.e. a timestamp at midnight";
    if (1970 - 12 - 31 <= $Ds || $Ds <= 2100 - 1 - 1) {
      $err = "$err\n(did you forget the final 'T' in the timestamp?)";
    }
    die $err;
  }
  if (defined($De)) {
    my ($secDe, $minDe, $hrDe, $dayDe, $monDe, $yrDe) = localtime($De / 1000);
    $yrDe += 1900;
    if ($secDe != 0 || $minDe != 0 || $hrDe != 0) {
      my $err = "slot: De=$yrDe-$monDe-$day{De}T$hrDe:$minDe:$secDe is not a date, i.e. a timestamp at midnight";
      if (1970 - 12 - 31 <= $De || $De <= 2100 - 1 - 1) {
        $err = "$err\n(did you forget the final 'T' in the timestamp?)";
      }
      die $err;
    }
  }
  return &slot0($Ts, $Te, $Ds, $De);
}

sub slot0() {
  my ($Ts, $Te, $Ds, $De) = @_;
  return sub(){ return &slot_Ts_Te(@_, $Ts, $Te, $Ds, $De); }
}

sub slot_Ts_Te() {
  my ($t, $ref_res, $resval, $Ts, $Te, $Ds, $De) = @_;
  if ($t == 0) { #initially
    my (undef, undef, undef, $day, $mon, $yr) = localtime($Ds / 1000);
    my ($secS, $minS, $hrS) = gmtime($Ts / 1000);
    my $D = timelocal($secS, $minS, $hrS, $day, $mon, $yr) * 1000;
    if ($D < 0) { # timeouts on negative times won't work, so start next day
      ($day, $mon, $yr) = &inc_date($day, $mon, $yr);
      $D = timelocal($secS, $minS, $hrS, $day, $mon, $yr) * 1000;
    }
    if (!defined($De) || $D < $De) {
      &set_timeout($D, $ref_res);
    }
    return 0;
  }
  # timeout
  &cancel_timeout($t, $ref_res);
  my (undef, undef, undef, $day, $mon, $yr) = localtime($t / 1000);
  if ($resval == 0) { # the resval returned will be 1
    if ($Ts > $Te) {
      ($day, $mon, $yr) = &inc_date($day, $mon, $yr);
    }
    my ($secE, $minE, $hrE) = gmtime($Te / 1000);
    my $D = timelocal($secE, $minE, $hrE, $day, $mon, $yr) * 1000;
    &set_timeout($D, $ref_res);
    return 1;
  }
  # the resval returned will be 0
  if ($Ts < $Te) {
    ($day, $mon, $yr) = &inc_date($day, $mon, $yr);
  }
  my $D = timelocal(0, 0, 0, $day, $mon, $yr) * 1000;
  if(!defined($De) || $D <= $De) {
    my ($secS, $minS, $hrS) = gmtime($Ts / 1000);
    $D = timelocal($secS, $minS, $hrS, $day, $mon, $yr) * 1000;
    &set_timeout($D, $ref_res);
  }
  return 0;
}

sub inc_date() {
  my ($d, $m, $y) = @_;
  my @ndays = (31, 29, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31);
  #print "y=$y,m=$m,d=$d,ndays[m]=$ndays[$m]\n";
  if ($d == $ndays[$m] ||
      $d == 28 && $m == 1 && !&leap($y)) {
    $d = 1;
    $m++;
    if ($m > 11) { $m = 0; $y++; }
  } else {
    $d++;
  }
  return ($d, $m, $y);
}

sub leap() {
  my ($y) = @_;
  return $y % 4 == 0 && $y % 100 != 0  || $y % 400 == 0;
}

# ------------------------------------------------------
# Duration operators, built into the language with infix syntax

# select intervals of p=1 shorter or equal to T
sub le() {
  my ($T) = @_;
  return \&false0 if $T <= 0;
  return sub(){ return &le1_T(@_, $T); }
}

sub le1_T() {
  my ($t, $ref_p, $ref_res, $resval, $T) = @_;
  if (&timeout($t, $ref_res)) {
   die "le1: escaped timer";
  }
  my $valp = &val($ref_p, $t);
  if ($t > 0 && &sameval($valp, &lastval($ref_p, $t))) { return $resval; } # nothing
  if(defined($valp) && $valp == 1) {# p=>1
    # p=1 until after t+T
    if(&later($ref_p, $t, 0, $T)) {
      &cancel_timeout($t + $T, $ref_res);
      return 0;
    } elsif(&soonereq($ref_p, $t, 0, $T)) {
      # p=>0 before or at t+T
      &cancel_timeout($t + $T, $ref_res);
      return 1;
    } else {
      &set_timeout($t + $T, $ref_res);
      return undef;
    }
  } elsif(defined($valp) && $valp == 0) {# p=>0
    return 0;
  } else {# p=> ?
    return undef;
  }
}

# select intervals of p=1 shorter than T
sub lt() {
  my ($T) = @_;
  return \&false0 if $T <= 1;
  return sub(){ return &lt1_T(@_, $T); }
}

sub lt1_T() {
  my ($t, $ref_p, $ref_res, $resval, $T) = @_;
  if (&timeout($t, $ref_res)) {
   die "lt1: escaped timer";
  }
  my $valp = &val($ref_p, $t);
  if($t > 0 && &sameval($valp, &lastval($ref_p, $t))) { return $resval; } # nothing
  if(defined($valp) && $valp == 1) {# p=>1
  # p=1 until at least t+T
    if(&latereq($ref_p, $t, 0, $T)) {
      &cancel_timeout($t + $T, $ref_res);
      return 0;
    } elsif(&sooner($ref_p, $t, 0, $T)) {
      # p=>0 before t+T
	    &cancel_timeout($t + $T, $ref_res);
	    return 1;
    } else {
      &set_timeout($t + $T, $ref_res);
      return undef;
    }
  } elsif(defined($valp) && $valp == 0) {# p=>0
    return 0;
  } else {# p=> ?
    return undef;
  }
}

# select intervals of p=1 longer than T
sub gt() {
  my ($T) = @_;
  return &id() if $T <= 0;
  return sub(){ return &gt1_T(@_, $T); }
}

sub gt1_T() {
  my ($t, $ref_p, $ref_res, $resval, $T) = @_;
  if (&timeout($t, $ref_res)) {
   die "gt1: escaped timer";
  }
  my $valp = &val($ref_p, $t);
  if($t > 0 && &sameval($valp, &lastval($ref_p, $t))) { return $resval; } # nothing
  if(defined($valp) && $valp == 1) {# p=>1
    # p=1 until after t+T
    if(&later($ref_p, $t, 0, $T)) {
    	&cancel_timeout($t + $T, $ref_res);
    	return 1;
    } elsif(&soonereq($ref_p, $t, 0, $T)) {
      # p=>0 before or at t+T
    	&cancel_timeout($t + $T, $ref_res);
    	return 0;
    } else {
      &set_timeout($t + $T, $ref_res);
      return undef;
    }
  } elsif(defined($valp) && $valp == 0) {# p=>0
    return 0;
  } else {# p=> ?
    return undef;
  }
}

# select intervals of p=1 longer than T
sub ge() {
  my ($T) = @_;
  return &id() if $T <= 1;
  return sub(){ return &ge1_T(@_, $T); }
}

sub ge1_T() {
  my ($t, $ref_p, $ref_res, $resval, $T) = @_;
  if (&timeout($t, $ref_res)) {
   die "ge1: escaped timer";
  }
  my $valp = &val($ref_p, $t);
  if($t > 0 && &sameval($valp, &lastval($ref_p, $t))) { return $resval; } # nothing
  if(defined($valp) && $valp == 1) {# p=>1
    # p=1 until at least t+T
    if(&latereq($ref_p, $t, 0, $T)) {
      &cancel_timeout($t + $T, $ref_res);
      return 1;
    } elsif(&sooner($ref_p, $t, 0, $T)) {
      # p=>0 before t+T
      &cancel_timeout($t + $T, $ref_res);
      return 0;
    } else {
      &set_timeout($t + $T, $ref_res);
      return undef;
    }
  } elsif(defined($valp) && $valp == 0) {# p=>0
    return 0;
  } else {# p=> ?
    return undef;
  }
}

# Real-time version of gt1(): falls back to 0 at T
sub gtRT() {
  my ($T) = @_;
  return \&false0 if $T <= 0;
  return sub(){ return &gtRT1_T(@_, $T); }
}

sub gtRT1_T() {
  my ($t, $ref_p, $ref_res, $resval, $T) = @_;
  if (&timeout($t, $ref_res)) {
    # if here, we're in the middle of a p=1 interval longer than T, so end it
    &cancel_timeout($t, $ref_res);
    return 0;
  }
  my $valp = &val($ref_p, $t);
  if($t > 0 && &sameval($valp, &lastval($ref_p, $t))) { return $resval; } # nothing
  if(defined($valp) && $valp == 1) {# p=>1
    # p=1 until after t+T
    if(&later($ref_p, $t, 0, $T)) {
      # timer may be already set (if previously res=undef for unsufficient
      # lookahead) or not (if previously res=undef for p=>undef)
      &set_timeout($t + $T, $ref_res);
      return 1;
    } elsif(&soonereq($ref_p, $t, 0, $T)) {
      # p=>0 before or at t+T
      &cancel_timeout($t + $T, $ref_res);
      return 0;
    } else {
      &set_timeout($t + $T, $ref_res);
      return undef;
    }
  } elsif(defined($valp) && $valp == 0) {# p=>0
    return 0;
  } else {# p=> ?
    return undef;
  }
}

# Real-time version of geRT(): falls back to 0 at T
sub geRT() {
  my ($T) = @_;
  return \&false0 if $T <= 0;
  return sub(){ return &geRT_T(@_, $T); }
}

sub geRT_T() {
  my ($t, $ref_p, $ref_res, $resval, $T) = @_;
  if (&timeout($t, $ref_res)) {
    # if here, we're in the middle of a p=1 interval longer than T, so end it
    &cancel_timeout($t, $ref_res);
    return 0;
  }
  my $valp = &val($ref_p, $t);
  if($t > 0 && &sameval($valp, &lastval($ref_p, $t))) { return $resval; } # nothing
  if(defined($valp) && $valp == 1) {# p=>1
    # p=1 until at least t+T
    if(&latereq($ref_p, $t, 0, $T)) {
      # timer may be already set (if previously res=undef for unsufficient
      # lookahead) or not (if previously res=undef for p=>undef)
      &set_timeout($t + $T, $ref_res);
      return 1;
    } elsif(&sooner($ref_p, $t, 0, $T)) {
      # p=>0 before t+T
      &cancel_timeout($t + $T, $ref_res);
      return 0;
    } else {
      &set_timeout($t + $T, $ref_res);
      return undef;
    }
  } elsif(defined($valp) && $valp == 0) {# p=>0
    return 0;
  } else {# p=> ?
    return undef;
  }
}

# Complementary real-time version of gtRT(): becomes 1 After T
sub gtRTa() {
  my ($T) = @_;
  return &id() if $T <= 0;
  return sub(){ return &gtRTa_T(@_, $T); }
}

sub gtRTa_T() {
  my ($t, $ref_p, $ref_res, $resval, $T) = @_;
  my $valp = &val($ref_p, $t);
  if (&timeout($t, $ref_res)) {
    # if here, we're at (p=>1)+T
    &cancel_timeout($t, $ref_res);
    if (defined($valp) && $valp  == 1) {
      return 1; # in the middle of an interval > T
    } else {
      return 0; # in the end of an interval = T
    }
  }
  if($t > 0 && &sameval($valp, &lastval($ref_p, $t))) { return $resval; } # nothing
  if(defined($valp) && $valp == 1) {# p=>1
    &set_timeout($t + $T, $ref_res);
    return 0;
  } elsif(defined($valp) && $valp == 0) {# p=>0
    my $t1 = &next_timeout($t, $ref_res);
    if (defined($t1)) {
      &cancel_timeout($t1, $ref_res);
    }
    return 0;
  } else {# p=> ?
    return undef;
  }
}

# ------------------------------------------------------
# Result structure
(
# Requires
{},
# Provides
{
"&" => [0,2, "p & q is the binary 'and' boolean operator,
(p&q)(t) <-> p(t) & q(t)"],
"|" => [0,2, "p | q is the binary 'or' boolean operator,
(p|q)(t) <-> p(t) or q(t)"],
"~" => [0,1, "~p is the unary 'not' boolean operator,
(~p)(t) <-> not p(t)"],
"<" => [1,1, "p < T selects the states of p shorter than T,
{[t,t') in p | t'-t < T}"],
">" => [1,1, "p > T selects the states of p longer than T,
{[t,t') in p | t'-t > T}"],
"<=" => [1,1, "p <= T selects the states of p lasting at most T,
{[t,t') in p | t'-t <= T}"],
">=" => [1,1, "p >= T selects the states of p lasting at least T,
{[t,t') in p | t'-t >= T}"],
">=!" => [1,1, "p >=! T selects the beginnings of states in p >= T, shortened to T,
{[t,t+T) | [t,t') in p & t'-t >= T}"],
">!" => [1,1, "p >! T selects the beginnings of states in p > T, shortened to T,
{[t,t+T) | [t,t') in p & t'-t > T}"],
">!!" => [1,1, "p >!! T selects the ends of states in p > T, after dropping p >! T,
{[t+T,t') | [t,t') in p & t'-t > T}"],
"true" => [0,0, "true is the constant signal always 1,
{[0,inf)}"],
"false" => [0,0, "false is the constant signal always 0,
{}"],
"id" => [0,1, "id(p) is the identity function for signals"],
"since" => [0,2,
"since(p,q) is the strong Since operator in LTL,
since(p,q)(t) <-> exists t'<=t . q(t') & p is 1 on (t',t]"],
"until" => [0,2,
"until(p,q) is the strong Until operator in LTL,
until(p,q)(t) <-> exists t'>=t . q(t') & p is 1 on [t,t')"],
"wsince" => [0,2, "wsince(p,q) is the weak Since operator in LTL,
wsince(p,q)(t) <-> since(p,q)(t) or forall t'<=t . p(t')"],
"wuntil" => [0,2, "wuntil(p,q) is the weak Until operator in LTL,
wuntil(p,q)(t) <-> until(p,q)(t) or forall t'>=t . p(t')"],
"delay" => [1,1,
"delay[T](p) produces the signal p delayed by T>0, padded with 0 at the origin,
{[t+T,t'+T) | [t,t') in p}"],
"wave" => [4,0,
"wave[T0,T1,Ts,Te] generates a periodic wave signal which is 0 during T0, then
1 during T1, starting at Ts and ending at Te,
{[Ts+(T0+T1)*n+T1,Ts+(T0+T1)*(n+1)) | n>=0 & Ts+(T0+T1)*n+T1 < Te }"],
"slot" => [undef,0, # really 3..4,0
"slot[Ts,Te,Ds(,De)?] generates a periodic slot signal which is 1 from Ts to Te
every day between Ds and De, and observing daylight saving time (DST)
NB: If De is omitted, the slot signal never ends (don't use it on finite logs)."]
},
# Contexts
[]
)
