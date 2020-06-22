#This converts the .doc files into more easily readable txt files

FILES:= $(patsubst %.doc,%.txt,$(wildcard *.doc))

doc:$(FILES)	
%.txt : %.doc
	sed -f ../../doc-to-help.sed $< > $@
clean:
	rm *.txt