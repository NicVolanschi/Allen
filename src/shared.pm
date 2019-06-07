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
# Module shared between the Allen compiler and virtual machine.
#

sub load() {
  my ($name) = @_;
  print STDERR "loading module $name...\n";
  if ($name !~ /^[.\/]/) { $name = "./$name"; } # default to current directory
  my @res = do "$name";
  die "error: $!\nwhen trying to load module \"$name\"\n$@" if $#res != 2;
  print STDERR "load result = $res\n" if defined($opts{'g'});
  #print STDERR "loaded $#$rules rules.\n";
  return @res;
}

# Load result
1
