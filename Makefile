main:
	xdg-open ./main.pdf && nohup typst watch ./main.typ &
done:
	rm -f nohup.out && pkill -f typst
build:
	rm -f ./main.pdf && typst compile ./main.typ -j 4
