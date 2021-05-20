@echo off

:: This requires the Windows Hypervisor Framework to be enabled.
::
::   Start Bar -> Search -> "Windows Features"
::             -> enable "Hyper-V" and "Windows Hypervisor Framework"
::
:: Executing the script will open a graphical console on the host,
:: and attach a virtual network device.
::
:: From the host you can then log into the guest using:
::  ssh -p 5555 artifact@localhost   (password is 'password')
::
:: The guest root account is          user:root      pw:password
:: The guest default user account is  user:artifact  pw:password
::
:: Start the guest system headless with '-display none'.
:: Use emulation instead of virtualization with '-accel tcg'.
::

qemu-system-x86_64^
    -name "ICFP 2021 Artifact"^
    -accel whpx -m 16384^
    -device e1000,netdev=net0^
    -netdev user,id=net0,hostfwd=tcp::5555-:22^
    -hda debian-artifact.qcow

