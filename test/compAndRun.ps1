stack run -- --basepath=../lib/ --disable-logging --overloading $args[0]
$path = [System.IO.Path]::GetDirectoryName($args[0])
Get-ChildItem -Path $path -Recurse -Include *.desugared.core, *.iridium, *.ll, *.test.core, *.exe | Remove-Item -Force

