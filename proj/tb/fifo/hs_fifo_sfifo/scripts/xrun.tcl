ida_database -open -name="ida.db"
ida_probe -log -sv_flow -log_objects -sv_modules -wave -wave_probe_args "-depth all -all -memories -variables -packed 4096 -unpacked 68 -dynamic"
ida_probe -log -sv_flow -log_objects -sv_modules -wave -wave_probe_args "DUV.sva_inst -depth 1 -assertions -transaction"
run
