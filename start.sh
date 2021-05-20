#!/bin/bash
set -u

#############################################################################
# Start the guest system.
#
#  This will open a graphical console on the host,
#  and attach a virtual network device.
#
#  From the host you can then log into the guest using:
#   ssh -p 5555 artifact@localhost   (password is 'password')
#
#  The guest root account is          user:root      pw:password
#  The guest default user account is  user:artifact  pw:password
#
#  Start the guest system headless with '-display none'.
#  Use emulation instead of virtualization with '-accel tcg'.
#
#############################################################################

# Expose all features present in the host cpu to the guest.
QEMU_CPU=max

# Give the guest 16GB of RAM.
QEMU_MEM_MB=16384

# Decide what virtualization method to use based on the host system.
case `uname` in
 'Darwin')
        # On Darwin we can use Apple's native
        #  Hardware Virtualization Framework (HVF)
        echo "Darwin host detected."
        QEMU_ACCEL=hvf
        ;;

 'Linux')
        # On Linux use the 'kvm' virtualization method.
        echo "Linux host detected."
        QEMU_ACCEL=kvm
        ;;

  *)    # By default use the Tiny Code Generator that dynamically
        #  converts guest instructions into host instructions.
        #  This is software emulation of the guest processor which
        #  is slow but reliable.
        echo "Unknown host system."
        QEMU_ACCEL=tcg
        ;;
esac

qemu-system-x86_64 \
        -name   "ICFP 2021 Artifact" \
        -accel  ${QEMU_ACCEL} \
        -cpu    ${QEMU_CPU} \
        -m      ${QEMU_MEM_MB} \
        -device e1000,netdev=net0 \
        -netdev user,id=net0,hostfwd=tcp::5555-:22 \
        -hda    debian-artifact.qcow \
        $@
