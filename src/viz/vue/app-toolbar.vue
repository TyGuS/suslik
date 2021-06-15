<template>
    <div class="proof-trace-toolbar">
        <div class="toolbox">
            <button @click="reload()">↻</button>
        </div>
        <form>
            Show:
            <input type="checkbox" name="proof-only" id="proof-only" v-model="options.proofOnly">
            <label for="proof-only">Proof only</label>
            <input type="checkbox" name="expanded-only" id="expanded-only" v-model="options.expandedOnly">
            <label for="expended-only">Expanded only</label>
        </form>
    </div>
</template>

<style>
div.proof-trace-toolbar {
    box-sizing: border-box;
    padding: 1em 1em .75em 1em;
}

div.proof-trace-toolbar .toolbox {
    float: right;
}
div.proof-trace-toolbar .toolbox button {
    font-size: 150%;
}
</style>

<script>
export default {
    props: {options: {default: () => ({})}},
    methods: {
        reload() {
            window.location.reload();
        }
    }
}
</script>
