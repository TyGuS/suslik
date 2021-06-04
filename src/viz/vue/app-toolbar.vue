<template>
    <div class="proof-trace-toolbar">
        <form>
            Show:
            <input type="checkbox" name="proof-only" id="proof-only" v-model="options.proofOnly">
            <label for="proof-only">Proof only</label>
            <input type="checkbox" name="expanded-only" id="expanded-only" v-model="options.expandedOnly">
            <label for="expended-only">Expanded only</label>
        </form>
    </div>
</template>

<script>
export default {
    props: {options: {default: () => ({})}}
}
</script>
