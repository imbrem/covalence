#!/usr/bin/env perl
use strict;
use warnings;
use File::Find;

my $root = shift // die "usage: $0 BOOK-DIRECTORY\n";
my (%top, %all, %includes);
my @edges;
my ($files, $lines, $forms) = (0, 0, 0);

my @files;
find(
    {
        no_chdir => 1,
        wanted   => sub {
            return unless -f $_ && /\.lisp\z/i && $File::Find::name !~ m{/(?:\.sys)/};
            push @files, $File::Find::name;
        },
    },
    $root
);

for my $file (sort @files) {
    open my $fh, '<', $file or die "$file: $!\n";
    local $/;
    my $text = <$fh>;
    close $fh;
    ++$files;
    $lines += 1 + ($text =~ tr/\n//);

    # This deliberately is a lexical inventory, not an ACL2 reader.  It handles
    # strings, escaped symbols, line comments, and nested block comments, which
    # is enough to identify list heads without macroexpanding the source.
    my @tokens;
    my $i = 0;
    while ($i < length $text) {
        my $c = substr($text, $i, 1);
        if ($c =~ /\s/) { ++$i; next }
        if ($c eq ';') {
            my $nl = index($text, "\n", $i);
            $i = $nl < 0 ? length($text) : $nl + 1;
            next;
        }
        if (substr($text, $i, 2) eq '#|') {
            my $depth = 1;
            $i += 2;
            while ($i < length($text) && $depth) {
                if (substr($text, $i, 2) eq '#|') { ++$depth; $i += 2 }
                elsif (substr($text, $i, 2) eq '|#') { --$depth; $i += 2 }
                else { ++$i }
            }
            next;
        }
        if ($c eq '"') {
            my $start = $i++;
            while ($i < length $text) {
                my $d = substr($text, $i++, 1);
                if ($d eq '\\') { ++$i }
                elsif ($d eq '"') { last }
            }
            push @tokens, substr($text, $start, $i - $start);
            next;
        }
        if ($c eq '|') {
            my $start = $i++;
            while ($i < length $text) {
                my $d = substr($text, $i++, 1);
                if ($d eq '\\') { ++$i }
                elsif ($d eq '|') { last }
            }
            push @tokens, substr($text, $start, $i - $start);
            next;
        }
        if ($c eq '(' || $c eq ')' || $c eq "'" || $c eq '`' || $c eq ',') {
            push @tokens, $c;
            ++$i;
            next;
        }
        my $start = $i;
        ++$i while $i < length($text)
            && substr($text, $i, 1) !~ /[\s();'",`]/;
        push @tokens, lc substr($text, $start, $i - $start);
    }

    my $depth = 0;
    for (my $n = 0; $n < @tokens; ++$n) {
        if ($tokens[$n] eq '(') {
            my $head = $tokens[$n + 1] // '';
            if ($head ne '' && $head ne '(' && $head ne ')') {
                ++$all{$head};
                if ($depth == 0) {
                    ++$top{$head};
                    ++$forms;
                }
            }
            ++$depth;
        } elsif ($tokens[$n] eq ')') {
            --$depth if $depth;
        }
    }

    while ($text =~ /\(\s*include-book\s+"([^"]+)"([^)]*)\)/sig) {
        my ($target, $tail) = ($1, lc $2);
        my $dir = $tail =~ /:dir\s+:([a-z0-9_-]+)/ ? $1 : 'relative';
        ++$includes{"$dir\t$target"};
        (my $relative = $file) =~ s{^\Q$root\E/?}{};
        push @edges, [$relative, $dir, $target];
    }
}

print "summary\tfiles\t$files\nsummary\tlines\t$lines\nsummary\ttop_forms\t$forms\n";
for my $name (sort { $top{$b} <=> $top{$a} || $a cmp $b } keys %top) {
    print "top\t$name\t$top{$name}\n";
}
for my $name (sort { $all{$b} <=> $all{$a} || $a cmp $b } keys %all) {
    print "all\t$name\t$all{$name}\n";
}
for my $key (sort keys %includes) {
    print "include\t$key\t$includes{$key}\n";
}
for my $edge (sort { join("\t", @$a) cmp join("\t", @$b) } @edges) {
    print "edge\t", join("\t", @$edge), "\n";
}
