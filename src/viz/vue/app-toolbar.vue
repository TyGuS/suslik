<template>
    <div class="proof-trace-toolbar">
        <div class="toolbox">
            <button @click="action('restart')">↻</button>
        </div>
        <form>
            <!--
            Show:
            <input type="checkbox" name="proof-only" id="proof-only" v-model="options.proofOnly">
            <label for="proof-only">Proof only</label>
            <input type="checkbox" name="expanded-only" id="expanded-only" v-model="options.expandedOnly">
            <label for="expended-only">Expanded only</label>
            -->
            <span style="margin-left: 2em">Traditional</span>
            <slider-switch v-model="options.simple"></slider-switch>
            <span>Simplified</span>

            <span style="margin-left: 2em">Manual</span>
            <slider-switch v-model="options.auto"></slider-switch>
            <span>Auto</span> 
        </form>
    </div>
</template>

<style>
div.proof-trace-toolbar {
    box-sizing: border-box;
}

div.proof-trace-toolbar form {
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
import SliderSwitch from './widgets/slider-switch.vue';


export default {
    props: {options: {default: () => ({})}},
    methods: {
        action(type) {
            this.$emit('action', {type});
        }
    },
    components: { SliderSwitch }
}
</script>
