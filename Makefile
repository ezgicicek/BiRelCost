# Program main file

# Ocamlbuild
OCBOPTS=-use-ocamlfind -pkg unix,menhirLib,why3,core,oUnit -tag debug,thread  -cflags -g
OCAMLBUILD=ocamlbuild $(OCBOPTS)

VERSION=byte


NAME=birel
# Program main file
MAIN=src/$(NAME)

TEST=src/test

.PHONY: $(NAME) clean clean-py $(NAME).byte $(NAME).native $(NAME).d.byte $(NAME).d.native 

all: $(NAME)

$(NAME): $(NAME).$(VERSION)
	cp $(NAME).$(VERSION) $(NAME)


runtime:
	$(MAKE) -C runtime

test:
	$(OCAMLBUILD) $(TEST).byte

$(NAME).byte:
	$(OCAMLBUILD) $(MAIN).byte

$(NAME).native:
	$(OCAMLBUILD) $(MAIN).native

$(NAME).p.byte:
	$(OCAMLBUILD) $(MAIN).p.byte

$(NAME).d.byte:
	$(OCAMLBUILD) $(MAIN).d.byte

$(NAME).p.native:
	$(OCAMLBUILD) $(MAIN).p.native

clean::
	$(OCAMLBUILD) -clean
	rm -f src/parser.conflicts
	rm -rf $(NAME) $(NAME).* $(NAME).exe TAGS



