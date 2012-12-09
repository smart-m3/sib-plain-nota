
bin_PROGRAMS = sib-plain-nota

# Compiler flags
sib_plain_nota_CFLAGS  = -Wall -I$(top_srcdir) -I$(top_srcdir)/include 
sib_plain_nota_CFLAGS += @GNOME_CFLAGS@ @LIBSIB_CFLAGS@ @NOTA_CFLAGS@


# Linker flags
sib_plain_nota_LDFLAGS = @GNOME_LIBS@ @LIBSIB_LIBS@ -lexpat @NOTA_LIBS@ -lm3_parse_n_gen

AM_CFLAGS = $(test_sib_CFLAGS) -g
# Put these in alphabetical order so that they are easy to find.

sib_plain_nota_SOURCES = \
	main.c 


