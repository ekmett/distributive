build:
	@cabalc build

install:
	@cabalc install

watch:
	@ghcid

uninstall: 
	@rm -rf ../dist-newstyle/build/*/*/make-0/

over: uninstall build

tags: $(wildcard **/*.hs)
	@fast-tags -R src

clean:
	@rm tags

.PHONY: build install watch uninstall over clean
