all: slides.pdf

%.pdf: %.typ
	@echo "Compiling $< to $@..."
	typst compile $< $@
