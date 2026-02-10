failing-builds.txt :
	grep "build failed" build-logs/* | cut -d ':' -f 1 | xargs -I % basename % | cut -d '.' -f 1 | sort -n > $@
