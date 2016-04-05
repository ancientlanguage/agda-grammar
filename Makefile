everything :
	@echo "module Everything where" > src/Everything.agda
	@find src -name '*.agda' -not -path 'src/Everything.agda' | sed -e 's/src\///;s/\//./g;s/\.agda$$//;s/^/import /' >> src/Everything.agda

