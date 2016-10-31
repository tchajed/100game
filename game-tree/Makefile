100game.svg: 100game.dot
	dot -Tsvg 100game.dot -o $@

100game.dot: 100game.py
	./100game.py

.PHONY: clean
clean:
	rm -f 100game.svg 100game.dot
