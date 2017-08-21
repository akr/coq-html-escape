require 'mkmf'

$CFLAGS << " -msse4.2"

create_makefile("verified_html_escape")
