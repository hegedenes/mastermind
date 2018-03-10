FRP_DIR   = ~/a/agda/frp/agda-frp-js

##
#  Don't modify from here
##

SRC_JS = require agda.frp agda.frp.main agda.frp.signal agda.frp.time agda.frp.taskqueue agda.mixin agda.box agda.array agda.keys agda.object

DEMO_AGDA = Mastermind
DEMO_HTML = main
DEMO_CSS  = mastermind

DIST_FILES = $(addprefix dist/, \
  $(addsuffix .js,$(SRC_JS)) \
  $(addprefix jAgda.,$(addsuffix .js,$(DEMO_AGDA))) \
  $(addsuffix .html,$(DEMO_HTML)) \
  $(addsuffix .css,$(DEMO_CSS)))

all: main

dist/:
	mkdir dist

dist/%.html: src/html/%.html
	cp $< $@

dist/%.css: src/html/%.css
	cp $< $@

dist/%.js: $(FRP_DIR)/src/js/%.js
	cp $< $@

.SECONDEXPANSION:
dist/jAgda.%.js: src/agda/$$(subst .,/,$$*).agda $(FRP_DIR)/src/agda/FRP/JS/*.agda $(FRP_DIR)/src/agda/FRP/JS/*/*.agda src/agda/*.agda src/agda/*/*.agda
	agda -i $(FRP_DIR)/src/agda -i src/agda --js --compile-dir dist $<

main: dist/ $(DIST_FILES)

clean:
	rm -rf dist
